//
// GCC-firm Project
//
// $Id$
//
// Testprogram to test GCC-firm : Args.c

#include <stdio.h>

static int id_0(int i, int j) {
  //int k;
  //k = 0;
  return(i);
}

int id_1(int i, int j) {
  //int k;
  //k = 0;
  return(i);
}

int main (int argc, char *argv[]) {
  //int k, i;
  printf("Args.c\n");
  return id_0(0,2) + id_1(0,2);
}
