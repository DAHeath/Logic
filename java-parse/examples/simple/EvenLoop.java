public class EvenLoop {
    public static void loop(int n) {
        int i = 0;
        while (i < n) {
            i = i + 2;
        }
        Wunderhorn.ensure(i != 41);
    }
}
