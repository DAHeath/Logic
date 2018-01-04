public class Pow {
  // https://leetcode.com/problems/powx-n/discuss/19593
  public double pow1(double x, int m) {
    double t = x;
    if(m == 0) {
      return 1;
    } else {
      t = pow1(x, m/2);
      if(m % 2 == 0) {
        return t*t;
      } else if (m > 0) {
        return x*t*t;
      } else {
        return (t*t)/x;
      }
    }
  }

  // https://leetcode.com/problems/powx-n/discuss/19566/
  public double pow2(double x, int n) {
    long m = n > 0 ? n : -(long)n;
    double ans = 1.0;
    while (m != 0) {
      if ((m & 1) == 1)
        ans *= x;
      x *= x;
      m >>= 1;
    }
    return n >= 0 ? ans : 1 / ans;
  }
}
