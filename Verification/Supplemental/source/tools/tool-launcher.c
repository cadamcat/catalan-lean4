#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

int main(int argc, char **argv) {
#ifdef LAKE_WRAPPER
  setenv("LAKE_NO_CACHE", "true", 1);
  setenv("LAKE_ARTIFACT_CACHE", "false", 1);
  setenv("MATHLIB_NO_CACHE_ON_UPDATE", "1", 1);
  setenv("LAKE_CACHE_DIR", "", 1);
  setenv("LEAN_NUM_THREADS", "16", 1);
  argv[0] = "/opt/lean-4.33.1/bin/lake-original";
  execv(argv[0], argv);
#else
  char **next = calloc((size_t)argc + 2, sizeof(char *));
  if (!next) return 125;
  next[0] = "/opt/lean-4.33.1/bin/python3-audit";
  next[1] = "/opt/lean-4.33.1/bin/lean-audit.py";
  for (int i = 1; i < argc; ++i) next[i + 1] = argv[i];
  execv(next[0], next);
#endif
  perror("audit tool launcher");
  return 126;
}
