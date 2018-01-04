class Mult {
  static int mult(int x, int y) {
    if (y == 0) {
      return 0;
    } else {
      return x + mult(x, y-1);
    }
  }

  static int mult_acc(int x, int y, int a) {
    if (y == 0) {
      return a;
    } else {
      return mult_acc(x, y-1, a+x);
    }
  }

  static int distR1(int x, int y, int z) {
    return mult(x+y, z);
  }

  static int distR2(int x, int y, int z) {
    return mult(x, z) + mult(y, z);
  }

  static int distL1(int x, int y, int z) {
    return mult(x, y+z);
  }

  static int distL2(int x, int y, int z) {
    return mult(x, y) + mult(x, z);
  }
}
