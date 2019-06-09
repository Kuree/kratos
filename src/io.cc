#include <fstream>
#include "io.hh"

bool exists(const std::string &filename) {
    std::ifstream in(filename);
    return in.good();
}