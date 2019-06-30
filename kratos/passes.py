from _kratos.passes import uniquify_generators as _uniquify_generators, \
    hash_generators as _hash_generators
from .generator import Generator
import enum
import _kratos


class HashStrategy(enum.Enum):
    SequentialHash = _kratos.HashStrategy.SequentialHash
    ParallelHash = _kratos.HashStrategy.ParallelHash


def uniquify_generators(generator: Generator):
    _uniquify_generators(generator.internal_generator)


def hash_generators(generator: Generator,
                    strategy: HashStrategy = HashStrategy.SequentialHash):
    _hash_generators(generator.internal_generator, strategy.value)
