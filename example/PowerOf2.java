// https://leetcode.com/problems/power-of-two/discuss/63966
class PowerOf2 {
  public static boolean powerOf2_1(int n) {
    if(n == 0) {
      return false;
    } else {
      while (n%2==0) {
        n /= 2;
      }
      return (n==1);
    }
  }

  public static boolean powerOf2_2(int n) {
    return n > 0 && (n==1 || (n % 2 == 0 && powerOf2_2(n/2)));
  }
}
