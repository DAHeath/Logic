class Sum {
  static int sum(int n) {
    if (n < 0) {
      return n + sum(n+1);
    } else if (n == 0) {
      return 0;
    } else {
      return n + sum(n-1);
    }
  }

  static int sum_acc(int n, int a) {
    if (n < 0) {
      return sum_acc(n+1, a+n);
    } else if (n == 0) {
      return a;
    } else {
      return sum_acc(n-1, a+n);
    }
  }
}
