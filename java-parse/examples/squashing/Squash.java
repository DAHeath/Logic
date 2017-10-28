public class Squash {

    public int canSquash(boolean p, boolean q) {
        int x = 0, y = 0, z = 0;
        if (p && q) {
            x = 3;
            y = 7;
        } else {
            x = 4;
            if (q) {
                z = 1;
            } else {
                z = 7;
            }
        }
        return x + y + z;
    }


    public int cannotSquash(boolean p) {
        int x = 0, y = 0;
        if (p) {
            x = 3;
            y = 7;
        } else {
            x = 4;
            while (x < 40) {
                x = x + 1;
            }
        }
        return x + y;
    }
}
