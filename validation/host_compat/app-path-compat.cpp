// Workspace-only compatibility adapter: supply the known toolchain location
// when the host does not expose /proc/self/exe. No proof/checker code changes.
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <dlfcn.h>
#include <unistd.h>

extern "C" ssize_t readlink(const char* path, char* buf, size_t size) {
    using Readlink = ssize_t (*)(const char*, char*, size_t);
    static auto real_readlink = reinterpret_cast<Readlink>(dlsym(RTLD_NEXT, "readlink"));
    ssize_t result = real_readlink(path, buf, size);
    if (result >= 0) return result;
    char own_path[128];
    std::snprintf(own_path, sizeof(own_path), "/proc/%d/exe", getpid());
    if (std::strcmp(path, own_path) != 0) return result;
    const char* known = std::getenv("TRANSPARENCY_LEAN_APP_PATH");
    if (!known) return result;
    size_t length = std::strlen(known);
    if (length > size) length = size;
    std::memcpy(buf, known, length);
    return static_cast<ssize_t>(length);
}
