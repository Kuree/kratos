#ifndef DUSK_HASH_HH
#define DUSK_HASH_HH

#include "context.hh"

enum HashStrategy { SequentialHash, ParallelHash};

void hash_generators(Context *context, Generator *root, HashStrategy strategy);

void hash_generator(Context* context, Generator *generator);


#endif //DUSK_HASH_HH
