#include <bits/stdc++.h>
using namespace std;


string toLen(int x, string st){
    while (st.size() < x){
        st = " " + st;
    }
    return st;
}
struct Symplex {
    struct Fraq {
        int a = 0, b = 1;
        Fraq() = default;
        Fraq(int a, int b): a(a), b(b){
            norm();
        }
        Fraq(int a): a(a){
            b = 1;
        }
        void norm(){
            int g = __gcd(a, b);
            a /= g;
            b /= g;
            if (b < 0){
                a *= -1;
                b *= -1;
            }
        }
        Fraq& operator += (const Fraq& other){
            int a1 = a * other.b;
            int a2 = other.a * b;
            a = a1 + a2;
            b = b * other.b;
            norm();
            return *this;
        }
        Fraq operator + (const Fraq& other) const {
            Fraq res = *this;
            res += other;
            return res;
        }

        Fraq& operator -= (const Fraq& other){
            int a1 = a * other.b;
            int a2 = other.a * b;
            a = a1 - a2;
            b = b * other.b;
            norm();
            return *this;
        }
        Fraq operator - (const Fraq& other) const {
            Fraq res = *this;
            res -= other;
            return res;
        }

        Fraq& operator *= (const Fraq& other){
            a *= other.a;
            b *= other.b;
            norm();
            return *this;
        }
        Fraq operator * (const Fraq& other) const {
            Fraq res = *this;
            res *= other;
            return res;
        }

        Fraq& operator /= (const Fraq& other){
            a *= other.b;
            b *= other.a;
            norm();
            return *this;
        }
        Fraq operator / (const Fraq& other) const {
            Fraq res = *this;
            res /= other;
            return res;
        }

        bool operator == (const Fraq& other) const {
            return a == other.a && b == other.b;
        }
        bool operator != (const Fraq& other) const {
            return !(*this == other);
        }
        bool operator < (const Fraq& other) const {
            auto res = *this - other;
            return (res.a < 0);
        }

        string toString() const {
            if (b == 1){
                return to_string(a);
            } else {
                return to_string(a) + "/" + to_string(b);
            }
        }

        static int nsk(int a, int b){
            return (a * b) / __gcd(a, b);
        }
    };
    struct Node {
        Fraq k1 = 0;
        Fraq kM = 0;
        Node() = default;
        Node(Fraq k1, Fraq kM) : k1(k1), kM(kM) {}
        Node& operator += (const Node& other){
            this -> k1 += other.k1;
            this -> kM += other.kM;
            return *this;
        }

        Node operator + (const Node& other) const {
            Node res = *this;
            res += other;
            return res;
        }

        Node& operator -= (const Node& other){
            this -> k1 -= other.k1;
            this -> kM -= other.kM;
            return *this;
        }

        Node operator - (const Node& other) const {
            Node res = *this;
            res -= other;
            return res;
        }

        Node& operator *= (const Node& other){
            this -> k1 *= other.k1;
            this -> kM *= other.k1;
            if (other.kM != 0){
                cerr << "Mul called with M > 0" << endl;
                exit(1);
            }
            return *this;
        }

        Node operator * (const Node& other) const {
            Node res = *this;
            res *= other;
            return res;
        }

        string toString() const {
            string res;
            if (k1 != 0 && kM != 0){
                res += "(" + k1.toString() + ", " + kM.toString() + "M)";
            } else if (k1 != 0){
                res += k1.toString();
            } else if (kM != 0){
                res += kM.toString() + "M";
            } else {
                res += "0";
            }
            return res;
        }


    };
    int n; // cnt of x's including p0
    int m; // cnt of restrictions
    vector<vector<Node>> v;
    vector<pair<int, Node>> B_CB;
    vector<Node> koef;
    vector<bool> banned;
    vector<bool> toBan;
    Symplex(int n, int m, vector<vector<Node>> v, vector<pair<int, Node>> b_cb, vector<Node> koef,
            vector<bool> toBan): n(n), m(m) , v(v), B_CB(b_cb), koef(koef), toBan(toBan){
        banned.assign(n, false);
    }
    Symplex(int n, int m, vector<vector<Node>> v, vector<pair<int, Node>> b_cb, vector<Node> koef,
            vector<bool> toBan, vector<bool> banned): n(n), m(m) , v(v), B_CB(b_cb), koef(koef), toBan(toBan), banned(banned){
    }
    void recalc(){
        calcSums();
        int colNum = findColToKick();
        int rowNum = findRowToKick(colNum);
        auto keyEl = v[rowNum][colNum];
        cout << "KeyEl: " + keyEl.toString() << endl;
        int ind = (B_CB[rowNum].first);
        if (toBan[ind]){
            banned[ind] = true;
        }
        getNewTable(colNum, rowNum, keyEl);
    }
    void getNewTable(int newBasis, int rowKicked, Node keyEl){
        vector<pair<int, Node>> B_CB_new = getNewBCB(newBasis, rowKicked, B_CB);
        vector<bool> readyCols(n, false);
        cout << "Filing one columns:" << endl;
        vector<vector<Node>> v_new = getOneCols(B_CB_new, readyCols);
        cout << Symplex(n, m, v_new, B_CB_new, koef, toBan, banned).toString() << endl;
        cout << "Dividing row we kicked:" << endl;
        divideRow(v_new, rowKicked, keyEl);
        cout << Symplex(n, m, v_new, B_CB_new, koef, toBan, banned).toString() << endl;
        cout << "Filling left cells with triagle rule: " << endl;
        fillTriangleRule(v_new, rowKicked, newBasis, readyCols);
        B_CB = B_CB_new;
        v = v_new;
        cout << toString() << endl;
        cout << "Calculating sums: " << endl;
        calcSums();
        cout << toString() << endl;

    }
    void fillTriangleRule(vector<vector<Node>>& v_new, int rowKicked, int colKicked, const vector<bool>& readyCols){
        for (int i = 0; i < m; i++){
            if (rowKicked == i){
                continue;
            }
            for (int j = 0; j < n; j++){
                if (!readyCols[j] && !banned[j]){
                    cout << v[i][j].k1.toString() << " - " << v[i][colKicked].k1.toString() << " * "  << v_new[rowKicked][j].k1.toString();
                    v_new[i][j].k1 = v[i][j].k1 - (v[i][colKicked].k1 * v_new[rowKicked][j].k1);
                    cout << " = " << v_new[i][j].k1.toString() << endl;
                }
            }
        }
    }
    void divideRow(vector<vector<Node>>& v_new, int rowKicked, const Node& keyEl){
        for (int i = 0; i < n; i++){
            v_new[rowKicked][i] = Node(v[rowKicked][i].k1 / keyEl.k1, 0);
        }
    }
    vector<vector<Node>> getOneCols(const vector<pair<int, Node>>& B_CB_new, vector<bool>& readyCols){
        vector<vector<Node>> v_new(m + 1);
        for (int i = 0; i <= m; i++){
            v_new[i].assign(n, Node(0, 0));
        }
        for (int i = 0; i < m; i++){
            v_new[i].resize(n);
            int col_indx = B_CB_new[i].first;
            for (int ii = 0; ii <= m; ii++){
                if (ii == i){
                    v_new[ii][col_indx] = Node(1, 0);
                } else {
                    v_new[ii][col_indx] = Node(0, 0);
                }
            }
            readyCols[col_indx] = true;
        }
        return v_new;
    }
    vector<pair<int, Node>> getNewBCB(int newBasis, int rowKicked, vector<pair<int, Node>> old_B_CB){
        vector<pair<int, Node>> B_CB_new = old_B_CB;
        B_CB_new[rowKicked].first = newBasis;
        B_CB_new[rowKicked].second = koef[newBasis];
        return B_CB_new;
    }
    int findColToKick(){
        int colNum = 0;
        Node val = Node(100000, 100000);
        for (int i = 0; i < n; i++){
            if (banned[i]){
                continue;
            }
            if (v[m][i].kM < val.kM){
                val = v[m][i];
                colNum = i;
            } else if (v[m][i].kM == val.kM){
                if (v[m][i].k1 < val.k1){
                    val = v[m][i];
                    colNum = i;
                }
            }
        }
        cout << "Column to kick: " + to_string(colNum) << endl;
        return colNum;
    }
    int findRowToKick(int col){
        int rowNum = -1;
        Fraq val = 1000000;
        for (int i = 0; i < m; i++){
            if (Fraq(0) < v[i][col].k1) {
                auto cur = v[i][0].k1 / v[i][col].k1;
                if (cur < val){
                    rowNum = i;
                    val = cur;
                }
            }
        }
        cout << "Row to kick: " << rowNum << endl;
        return rowNum;
    }
    void calcSums(){
        for (int j = 0; j < n; j++){
            v[m][j] = Node(0, 0);
            for (int i = 0; i < m; i++){
                v[m][j] += B_CB[i].second * v[i][j];
            }
            v[m][j] -= koef[j];
        }
        cout << "Sums done" << endl;
    }
    string toString() const {
        // row 1
        string empty(10, ' ');
        string res;
        res += empty + " " + empty + " ";
        for (int i = 0; i < n; i++){
            res += toLen(10, koef[i].toString()) + " ";
        }
        res += "\n";
        // row 2
        res += empty + " " + empty + " ";
        for (int i = 0; i < n; i++){
            res += toLen(10, "p" + to_string(i)) + " ";
        }
        res += "\n";
        // main table
        for (int i = 0; i < m; i++){
            res += toLen(10, "p" + to_string(B_CB[i].first)) + " ";
            res += toLen(10, B_CB[i].second.toString()) + " ";
            for (int j = 0; j < n; j++){
                if (!banned[j]) {
                    res += toLen(10, v[i][j].toString()) + " ";
                } else {
                    res += string(10, '-') + " ";
                }
            }
            res += "\n";
        }
        // summary rows
        res += empty + " " + empty + " ";
        for (int j = 0; j < n; j++){
            if (!banned[j]) {
                res += toLen(10, v[m][j].toString()) + " ";
            } else {
                res += string(10, '-') + " ";
            }
        }
        return res;
    }
};



ostream& operator<< (ostream& stream, const Symplex& s){
    stream << s.toString();
    return stream;
}


int main() {
    int n, m;
    cout << "Insert num of x's: ";
    cin >> n;
    cout << "Insert num of restrictions: ";
    cin >> m;
    cout << "Print coef near each p_i in an other line. i:[0, " + to_string(n) +"). a + b*M \n";
    vector<Symplex::Node> koef(n);
    for (int i = 0; i < n; i++){
        int a, b;
        cin >> a >> b;
        koef[i].k1 = a;
        koef[i].kM = b;
    }
    cout << "Print num of var and koef\n";
    vector<pair<int, Symplex::Node>> cb(m);
    for (int i = 0; i < m; i++){
        int a, b, c;
        cin >> a >> b >> c;
        cb[i].first = a;
        cb[i].second = Symplex::Node(b, c);
    }
    cout << "Insert table with summary line of 0" << endl;
    vector<vector<Symplex::Node>> v(m + 1);
    for (int i = 0; i <= m; i++){
        v[i].resize(n);
        for (int j = 0; j < n; j++){
            int a;
            cin >> a;
            v[i][j] = Symplex::Node(a, 0);
        }
    }
    vector<bool> toBan(n, false);
    cout << "Insert shtuchni indexes count, then indexes:" << endl;
    int k;
    cin >> k;
    for (int i = 0; i < k; i++){
        int a;
        cin >> a;
        toBan[a] = true;
    }
    auto s = Symplex(n, m, v, cb, koef, toBan);
    s.calcSums();
    cout << s.toString() << endl;
    int x;
    while(cin >> x) {
        if (x == 123) {
            s.recalc();
        }
    }
    return 0;
}
/*
v3
9
4
0 0
5 0
3 0
0 0
0 0
0 0
0 0
0 -1
0 -1

7 0 -1
4 0 0
5 0 0
8 0 -1

0 2 3 -1 0 0 -12 1 0
 0 -1 6 0 1 0 -18 0 0
 0 1 -3 0 0 1 -3 0 0
 1 1 3 0 0 0 0 0 1
 0 0 0 0 0 0 0 0 0
 2
7 8

 v1
 9 4

 0 0
-5 0
4 0
0 0
0 0
0 0
0 0
0 -1
0 -1

 3 0 0
 4 0 0
 7 0 -1
 8 0 -1

 0 2 -4 1 0 0 -12 0 0
 0 -1 2 0 1 0 -8 0 0
 0 1 1 0 0 -1 -10 1 0
 1 2 3 0 0 0 0 0 1
 0 0 0 0 0 0 0 0 0

 2
 7 8



 */