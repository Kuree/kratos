#ifndef KRATOS_HASH_HH
#define KRATOS_HASH_HH

#include "context.hh"

namespace kratos {

void hash_generators_context(Context *context, Generator *root, HashStrategy strategy);

uint64_t hash_64_fnv1a(const void* key, uint64_t len);

}  // namespace kratos

#endif  // KRATOS_HASH_HH
