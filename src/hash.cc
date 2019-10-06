#include "hash.hh"
#include <fstream>
#include "cxxpool.h"
#include "debug.hh"
#include "generator.hh"
#include "graph.hh"
#include "ir.hh"
#include "pass.hh"
#include "stmt.hh"
#include "util.hh"

namespace kratos {
/*
 * Once this project is moved to gcc-9, we will use the parallel execution
 * #include <numeric>
 * #include <execution>
 */

// Below code has minor changes to pass clang-tidy made by me (Keyi)
/// XXHash (64 bit), based on Yann Collet's descriptions, see http://cyan4973.github.io/xxHash/
/** How to use:
    uint64_t myseed = 0;
    XXHash64 myhash(myseed);
    myhash.add(pointerToSomeBytes,     numberOfBytes);
    myhash.add(pointerToSomeMoreBytes, numberOfMoreBytes); // call add() as often as you like to ...
    // and compute hash:
    uint64_t result = myhash.hash();

    // or all of the above in one single line:
    uint64_t result2 = XXHash64::hash(mypointer, numBytes, myseed);

    Note: my code is NOT endian-aware !
**/
class XXHash64 {
public:
    /// create new XXHash (64 bit)
    /** @param seed your seed value, even zero is a valid seed **/
    explicit XXHash64(uint64_t seed) : state(), buffer() {
        state[0] = seed + Prime1 + Prime2;
        state[1] = seed + Prime2;
        state[2] = seed;
        state[3] = seed - Prime1;
        bufferSize = 0;
        totalLength = 0;
    }

    /// add a chunk of bytes
    /** @param  input  pointer to a continuous block of data
        @param  length number of bytes
        @return false if parameters are invalid / zero **/
    bool add(const void* input, uint64_t length) {
        // no data ?
        if (!input || length == 0) return false;

        totalLength += length;
        // byte-wise access
        auto data = (const unsigned char*)input;

        // unprocessed old data plus new data still fit in temporary buffer ?
        if (bufferSize + length < MaxBufferSize) {
            // just add new data
            while (length-- > 0) buffer[bufferSize++] = *data++;
            return true;
        }

        // point beyond last byte
        const unsigned char* stop = data + length;
        const unsigned char* stopBlock = stop - MaxBufferSize;

        // some data left from previous update ?
        if (bufferSize > 0) {
            // make sure temporary buffer is full (16 bytes)
            while (bufferSize < MaxBufferSize) buffer[bufferSize++] = *data++;

            // process these 32 bytes (4x8)
            process(buffer, state[0], state[1], state[2], state[3]);
        }

        // copying state to local variables helps optimizer A LOT
        uint64_t s0 = state[0], s1 = state[1], s2 = state[2], s3 = state[3];
        // 32 bytes at once
        while (data <= stopBlock) {
            // local variables s0..s3 instead of state[0]..state[3] are much faster
            process(data, s0, s1, s2, s3);
            data += 32;
        }
        // copy back
        state[0] = s0;
        state[1] = s1;
        state[2] = s2;
        state[3] = s3;

        // copy remainder to temporary buffer
        bufferSize = stop - data;
        for (unsigned int i = 0; i < bufferSize; i++) buffer[i] = data[i];

        // done
        return true;
    }

    /// get current hash
    /** @return 64 bit XXHash **/
    [[nodiscard]] uint64_t hash() const {
        // fold 256 bit state into one single 64 bit value
        uint64_t result;
        if (totalLength >= MaxBufferSize) {
            result = rotateLeft(state[0], 1) + rotateLeft(state[1], 7) + rotateLeft(state[2], 12) +
                     rotateLeft(state[3], 18);
            result = (result ^ processSingle(0, state[0])) * Prime1 + Prime4;
            result = (result ^ processSingle(0, state[1])) * Prime1 + Prime4;
            result = (result ^ processSingle(0, state[2])) * Prime1 + Prime4;
            result = (result ^ processSingle(0, state[3])) * Prime1 + Prime4;
        } else {
            // internal state wasn't set in add(), therefore original seed is still stored in state2
            result = state[2] + Prime5;
        }

        result += totalLength;

        // process remaining bytes in temporary buffer
        const unsigned char* data = buffer;
        // point beyond last byte
        const unsigned char* stop = data + bufferSize;

        // at least 8 bytes left ? => eat 8 bytes per step
        for (; data + 8 <= stop; data += 8)
            result = rotateLeft(result ^ processSingle(0, *(uint64_t*)data), 27) * Prime1 + Prime4;

        // 4 bytes left ? => eat those
        if (data + 4 <= stop) {
            result = rotateLeft(result ^ (*(uint32_t*)data) * Prime1, 23) * Prime2 + Prime3;
            data += 4;
        }

        // take care of remaining 0..3 bytes, eat 1 byte per step
        while (data != stop) result = rotateLeft(result ^ (*data++) * Prime5, 11) * Prime1;

        // mix bits
        result ^= result >> 33u;
        result *= Prime2;
        result ^= result >> 29u;
        result *= Prime3;
        result ^= result >> 32u;
        return result;
    }

    /// combine constructor, add() and hash() in one static function (C style)
    /** @param  input  pointer to a continuous block of data
        @param  length number of bytes
        @param  seed your seed value, e.g. zero is a valid seed
        @return 64 bit XXHash **/
    static uint64_t hash(const void* input, uint64_t length, uint64_t seed) {
        XXHash64 hasher(seed);
        hasher.add(input, length);
        return hasher.hash();
    }

private:
    /// magic constants :-)
    static const uint64_t Prime1 = 11400714785074694791ULL;
    static const uint64_t Prime2 = 14029467366897019727ULL;
    static const uint64_t Prime3 = 1609587929392839161ULL;
    static const uint64_t Prime4 = 9650029242287828579ULL;
    static const uint64_t Prime5 = 2870177450012600261ULL;

    /// temporarily store up to 31 bytes between multiple add() calls
    static const uint64_t MaxBufferSize = 31 + 1;

    uint64_t state[4];                    // NOLINT
    unsigned char buffer[MaxBufferSize];  // NOLINT
    unsigned int bufferSize;
    uint64_t totalLength;

    /// rotate bits, should compile to a single CPU instruction (ROL)
    static inline uint64_t rotateLeft(uint64_t x, unsigned char bits) {
        return (x << bits) | (x >> (64u - bits));
    }

    /// process a single 64 bit value
    static inline uint64_t processSingle(uint64_t previous, uint64_t input) {
        return rotateLeft(previous + input * Prime2, 31) * Prime1;
    }

    /// process a block of 4x4 bytes, this is the main part of the XXHash32 algorithm
    static inline void process(const void* data, uint64_t& state0, uint64_t& state1,
                               uint64_t& state2, uint64_t& state3) {
        auto block = (const uint64_t*)data;
        state0 = processSingle(state0, block[0]);
        state1 = processSingle(state1, block[1]);
        state2 = processSingle(state2, block[2]);
        state3 = processSingle(state3, block[3]);
    }
};

// this is slower than xxhash
// but it's simple, so use it to hash the variables
// based on https://gist.github.com/underscorediscovery/81308642d0325fd386237cfa3b44785c
uint64_t hash_64_fnv1a(const void* key, uint64_t len) {
    auto data = static_cast<const char*>(key);
    uint64_t hash = 0xcbf29ce484222325;
    uint64_t prime = 0x100000001b3;

    for (uint64_t i = 0; i < len; ++i) {
        uint8_t value = data[i];
        hash = hash ^ value;
        hash *= prime;
    }

    return hash;

}  // hash_64_fnv1a

constexpr uint64_t shift_const(uint64_t value, uint8_t amount) {
    return (value << amount) | (value >> (64u - amount));
}

class HashVisitor : public IRVisitor {
public:
    explicit HashVisitor(Generator* root) : root_(root) {
        context_ = root->context();
        // compute the hash for all vars
        auto vars = root->get_vars();
        var_hashes_.reserve(vars.size());
        for (const auto& var : vars) {
            uint64_t var_hash = hash_64_fnv1a(var.c_str(), var.size());
            var_hashes_.emplace_back(var_hash);
        }
    }

    uint64_t produce_hash() {
        // use generator name as a seed
        uint64_t var_hash = hash_64_fnv1a(root_->name.c_str(), root_->name.size()) << 32u;
        for (const uint64_t var : var_hashes_) var_hash = var_hash ^ var;
        // use var_hash as a seed
        // FIXME: do we really need to hash in chunks? or can we use xor to ignore the ordering
        //  of the blocks?
        uint64_t result =
            XXHash64::hash(stmt_hashes_.data(), stmt_hashes_.size() * sizeof(uint64_t), var_hash);
        return result;
    }

    void visit(AssignStmt* stmt) override {
        auto var = stmt->left()->to_string() + stmt->right()->to_string() +
                   std::to_string(stmt->left()->width());
        uint64_t stmt_hash = hash_64_fnv1a(var.c_str(), var.size());
        // based on level
        stmt_hash = shift(stmt_hash, level);
        stmt_hashes_.emplace_back(stmt_hash);
    }

    void visit(IfStmt* stmt) override {
        // magic number comes from here https://stackoverflow.com/a/4948967
        // based on the requirements, warped shifting doesn't matter since it keeps
        // the number of 0 and 1 the same. And I don't think the shifting will
        // introduce any correlation either
        constexpr uint64_t if_signature = shift_const(0x9e3779b97f4a7c16, 1);
        auto var = stmt->predicate()->to_string();
        uint64_t hash = hash_64_fnv1a(var.c_str(), var.size()) << level;
        stmt_hashes_.emplace_back(if_signature ^ hash);
    }

    void visit(SwitchStmt* stmt) override {
        constexpr uint64_t switch_signature = shift_const(0x9e3779b97f4a7c16, 2);
        auto var = stmt->target()->to_string();
        uint64_t hash = hash_64_fnv1a(var.c_str(), var.size()) << level;
        stmt_hashes_.emplace_back(switch_signature ^ hash);
    }

    void visit(CombinationalStmtBlock*) override {
        constexpr uint64_t comb_signature = shift_const(0x9e3779b97f4a7c16, 3);
        stmt_hashes_.emplace_back(comb_signature << level);
    }

    void visit(SequentialStmtBlock* stmt) override {
        std::string cond;
        auto const& conditions = stmt->get_conditions();
        for (auto const& [type, var] : conditions) {
            if (type == BlockEdgeType::Posedge)
                cond.append("1" + var->to_string());
            else
                cond.append("0" + var->to_string());
        }
        uint64_t hash = hash_64_fnv1a(cond.c_str(), cond.size()) << level;
        constexpr uint64_t seq_signature = shift_const(0x9e3779b97f4a7c16, 3);
        stmt_hashes_.emplace_back(hash ^ seq_signature);
    }

    void visit(ModuleInstantiationStmt* stmt) override {
        // notice that we don't use any mechanism to lock the context's get hash or set hash
        // it is the caller's responsibility to do prepare the calling sequence so that there
        // won't be any race condition.
        // by requiring this, we can have a lock-free implementation ready to scale
        auto target = stmt->target();
        if (!context_->has_hash(target)) {
            throw std::runtime_error("Internal error: " + target->name + " doesn't have a hash");
        }
        uint64_t target_hash = context_->get_hash(target);
        constexpr uint64_t mod_signature = shift_const(0x9e3779b97f4a7c16, 4);
        // we have assign stmts already computed the connections
        stmt_hashes_.emplace_back(target_hash ^ mod_signature);
    }

    void visit(FunctionCallStmt* stmt) override {
        // this is to hash the call args and func_def
        auto func = stmt->func();
        auto str = func->function_name();
        if (str != break_point_func_name) {
            // breakpoint with id doesn't count since their ids will be different all the time
            auto const& var = stmt->var();
            auto const& var_args = var->args();
            // this is ordered map
            for (auto const& iter : var_args) {
                str.append(iter.second->to_string());
            }
        }
        uint64_t hash = hash_64_fnv1a(str.c_str(), str.size()) << level;
        constexpr uint64_t call_signature = shift_const(0x9e3779b97f4a7c16, 4);
        stmt_hashes_.emplace_back(hash ^ call_signature);
    }

private:
    std::vector<uint64_t> var_hashes_;
    std::vector<uint64_t> stmt_hashes_;
    Generator* root_;
    Context* context_;

    inline static uint64_t shift(uint64_t value, uint8_t amount) {
        return (value << amount) | (value >> (64u - amount));
    }
};

uint64_t hash_generator(Generator* generator) {
    // we use a visitor to compute all the hashes
    HashVisitor hash_visitor(generator);
    hash_visitor.visit_root(generator);
    return hash_visitor.produce_hash();
}

void hash_generator_src(Context* context, Generator* generator) {
    auto filename = generator->external_filename();
    std::ifstream fs(filename);

    std::string content;
    content.assign(std::istreambuf_iterator<char>(fs), std::istreambuf_iterator<char>());
    uint64_t hash = XXHash64::hash(content.c_str(), content.size(), 0);
    context->add_hash(generator, hash);
}

void hash_generator_name(Context* context, Generator* generator) {
    auto const& name = generator->name;
    uint64_t hash = hash_64_fnv1a(name.c_str(), name.size());
    context->add_hash(generator, hash);
}

void hash_generators_context(Context* context, Generator* root, HashStrategy strategy) {
    // clear the hash first
    context->clear_hash();

    // compute the generator graph
    GeneratorGraph g(root);
    // if it's sequential, do topological sort
    // if it's parallel, do level sort

    if (strategy == HashStrategy::SequentialHash) {
        auto const& sequence = g.get_sorted_generators();
        std::vector<Generator*> list;
        // reserve for list
        list.reserve(sequence.size());

        for (auto& node : sequence) {
            // different cases
            if (node->external()) {
                if (node->external_filename().empty()) {
                    // user marked external file, skip it
                    continue;
                } else {
                    hash_generator_src(context, node);
                }
            } else if (context->get_generators_by_name(node->name).size() == 1) {
                // just need to hash the name
                hash_generator_name(context, node);
            } else {
                // only the one being used
                if (node->parent() == nullptr && node != root) continue;
                list.emplace_back(node);
            }
        }
        for (auto const& node : list) {
            uint64_t hash = hash_generator(node);
            context->add_hash(node, hash);
        }
    } else if (strategy == HashStrategy::ParallelHash) {
        uint32_t num_cpus = get_num_cpus();
        cxxpool::thread_pool pool{num_cpus};

        auto levels = g.get_leveled_generators();
        // we proceed in a reversed order
        for (int i = static_cast<int>(levels.size() - 1); i >= 0; i--) {
            auto list = levels[i];
            std::vector<uint64_t> hash_values;
            std::vector<std::future<uint64_t>> thread_tasks;
            thread_tasks.reserve(list.size());

            for (auto const& node : list) {
                auto task = pool.push(hash_generator, node);
                thread_tasks.emplace_back(std::move(task));
            }

            cxxpool::get(thread_tasks.begin(), thread_tasks.end(), hash_values);
            for (uint64_t j = 0; j < list.size(); j++) {
                auto const& node = list[j];
                auto const hash = hash_values[j];
                context->add_hash(node, hash);
            }
        }
    }
}

}  // namespace kratos
