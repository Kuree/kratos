#include "vpi_user.h"
#include <sys/socket.h>
#include <unordered_set>
#include <condition_variable>
#include <mutex>

std::unordered_set<uint32_t> break_points;
std::mutex continue_mutex;
bool should_continue = false;
std::condition_variable continue_cv;


extern "C" {
    // breakpoint trace
    void breakpoint_trace(uint32_t id) {
        if (break_points.find(id) != break_points.end()) {
            std::unique_lock<std::mutex> lk(continue_mutex);
            continue_cv.wait(lk, []{ return should_continue; });
        }
    }

    // runtime initialization
    void initialize_runtime() {
        // we need to register two things
        // what to do when the simulation starts and what to do when the simulation ends
        // during the start time, we need to start the server and after the simulation ends
        // we need to tear down the server
    }
}