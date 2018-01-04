public class CanMeasureWater {
  // https://leetcode.com/problems/water-and-jug-problem/discuss/83738
  public static boolean canMeasureWater1(int x, int y, int z) {
    if(z==0) return true;
    if(z>x+y) return false;
    int g = gcd1(x,y);
    if(g==0) return false;
    else return z%g==0;
  }
  public static int gcd1(int a, int b) {
    if (b==0) return a;
    return gcd1(b,a%b);
  }

  // https://leetcode.com/problems/water-and-jug-problem/discuss/83715
  public static boolean canMeasureWater2(int x, int y, int z) {
    if(x + y < z) return false;
    if( x == z || y == z || x + y == z ) return true;

    return z%gcd2(x, y) == 0;
  }
  public static int gcd2(int a, int b){
    while(b != 0 ){
      int temp = b;
      b = a%b;
      a = temp;
    }
    return a;
  }

  // public static boolean canMeasureWaterTest(int x, int y, int z) {
  //   if(x + y < z) return false;
  //   if( x == z || y == z || x + y == z ) return true;

  //   return z%gcd1(x, y) == 0;
  // }
}
