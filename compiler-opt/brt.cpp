#include <cstdio>
#include <cstdint>

extern "C" void bf_main(uint8_t*, int*);

#if !defined(_WIN32) && !defined(__MINGW64__) && !defined(__MINGW32__)
extern "C" void _putchar(int ch) { putchar(ch); }
extern "C" int _getchar() { return getchar(); }
extern "C" void _bf_main(uint8_t*, int*);
void bf_main(uint8_t* ebx, int* edi) { _bf_main(ebx, edi); }
int _tmp;
#else
int tmp;
#endif

uint8_t mem[1048576];
int locals[1048576];

int main() {
  bf_main(mem + 514188, locals);
  return 0;
}
