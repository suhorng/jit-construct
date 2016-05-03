#include <cstdio>
#include <cstdint>

extern "C" void bf_main(uint8_t*, int*);
extern "C" int tmp;

uint8_t mem[1048576];
int locals[1048576];

int main() {
  bf_main(mem + 514188, locals);
  return 0;
}
