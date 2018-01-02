class Mult {
  static int mult(int x, int y) {
    if (y == 0) {
      return 0;
    } else {
      return x + mult(x, y-1);
    }
  }

  static int f(int x, int y, int z) {
    return mult(x, y+z);
  }

  static int g(int x, int y, int z) {
    return mult(x, y) + mult(x, z);
  }
}
