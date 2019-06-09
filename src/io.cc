#include "io.hh"
#include <fstream>

bool exists(const std::string &filename) {
    std::ifstream in(filename);
    return in.good();
}