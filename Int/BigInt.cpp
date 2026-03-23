#include <iostream>
#include <vector>
#include <string>
#include <stdexcept>
#include <algorithm>
#include <cctype>
#include <cstdint>

class BigInt {
private:
    static constexpr uint32_t BASE = 1000000000; // 1e9
    static constexpr int BASE_DIGITS = 9;

    bool is_neg = false;
    std::vector<uint32_t> limbs; // 低位在前存储

private:
    bool isZero() const {
        return limbs.size() == 1 && limbs[0] == 0;
    }

    void normalize() {
        while (limbs.size() > 1 && limbs.back() == 0) {
            limbs.pop_back();
        }
        if (limbs.empty()) {
            limbs.push_back(0);
        }
        if (isZero()) {
            is_neg = false;
        }
    }

    static int compareAbs(const BigInt& a, const BigInt& b) {
        if (a.limbs.size() != b.limbs.size()) {
            return (a.limbs.size() < b.limbs.size()) ? -1 : 1;
        }
        for (int i = static_cast<int>(a.limbs.size()) - 1; i >= 0; --i) {
            if (a.limbs[i] != b.limbs[i]) {
                return (a.limbs[i] < b.limbs[i]) ? -1 : 1;
            }
        }
        return 0;
    }

    static BigInt addAbs(const BigInt& a, const BigInt& b) {
        BigInt res;
        res.is_neg = false;
        res.limbs.clear();

        const size_t n = std::max(a.limbs.size(), b.limbs.size());
        uint64_t carry = 0;

        for (size_t i = 0; i < n || carry; ++i) {
            uint64_t cur = carry;
            if (i < a.limbs.size()) cur += a.limbs[i];
            if (i < b.limbs.size()) cur += b.limbs[i];
            res.limbs.push_back(static_cast<uint32_t>(cur % BASE));
            carry = cur / BASE;
        }

        res.normalize();
        return res;
    }

    // precondition: |a| >= |b|
    static BigInt subAbs(const BigInt& a, const BigInt& b) {
        BigInt res;
        res.is_neg = false;
        res.limbs.clear();

        int64_t carry = 0;
        for (size_t i = 0; i < a.limbs.size(); ++i) {
            int64_t cur = static_cast<int64_t>(a.limbs[i]) - carry;
            if (i < b.limbs.size()) cur -= b.limbs[i];

            if (cur < 0) {
                cur += BASE;
                carry = 1;
            } else {
                carry = 0;
            }

            res.limbs.push_back(static_cast<uint32_t>(cur));
        }

        res.normalize();
        return res;
    }

    static BigInt mulAbs(const BigInt& a, const BigInt& b) {
        BigInt res;
        res.is_neg = false;
        res.limbs.assign(a.limbs.size() + b.limbs.size(), 0);

        for (size_t i = 0; i < a.limbs.size(); ++i) {
            uint64_t carry = 0;
            for (size_t j = 0; j < b.limbs.size() || carry; ++j) {
                uint64_t cur = res.limbs[i + j] + carry;
                if (j < b.limbs.size()) {
                    cur += static_cast<uint64_t>(a.limbs[i]) * b.limbs[j];
                }
                res.limbs[i + j] = static_cast<uint32_t>(cur % BASE);
                carry = cur / BASE;
            }
        }

        res.normalize();
        return res;
    }

    static BigInt mulAbsUint32(const BigInt& a, uint32_t m) {
        if (m == 0) return BigInt(0);
        if (m == 1) return a.abs();

        BigInt res;
        res.is_neg = false;
        res.limbs.clear();

        uint64_t carry = 0;
        for (size_t i = 0; i < a.limbs.size() || carry; ++i) {
            uint64_t cur = carry;
            if (i < a.limbs.size()) {
                cur += static_cast<uint64_t>(a.limbs[i]) * m;
            }
            res.limbs.push_back(static_cast<uint32_t>(cur % BASE));
            carry = cur / BASE;
        }

        res.normalize();
        return res;
    }

    // cur = cur * BASE + digit
    void shiftBaseAndAdd(uint32_t digit) {
        if (isZero() && digit == 0) {
            return;
        }
        limbs.insert(limbs.begin(), digit);
        normalize();
    }

    static std::pair<BigInt, BigInt> divmodAbs(const BigInt& a, const BigInt& b) {
        if (b.isZero()) {
            throw std::runtime_error("division by zero");
        }

        if (compareAbs(a, b) < 0) {
            return {BigInt(0), a};
        }

        BigInt divisor = b.abs();
        BigInt current(0);

        BigInt quotient;
        quotient.is_neg = false;
        quotient.limbs.assign(a.limbs.size(), 0);

        for (int i = static_cast<int>(a.limbs.size()) - 1; i >= 0; --i) {
            current.shiftBaseAndAdd(a.limbs[i]);

            uint32_t left = 0;
            uint32_t right = BASE - 1;
            uint32_t best = 0;

            while (left <= right) {
                uint32_t mid = left + (right - left) / 2;
                BigInt prod = mulAbsUint32(divisor, mid);
                int cmp = compareAbs(prod, current);
                if (cmp <= 0) {
                    best = mid;
                    if (mid == BASE - 1) break;
                    left = mid + 1;
                } else {
                    if (mid == 0) break;
                    right = mid - 1;
                }
            }

            quotient.limbs[i] = best;
            if (best != 0) {
                current = subAbs(current, mulAbsUint32(divisor, best));
            }
        }

        quotient.normalize();
        current.normalize();
        return {quotient, current};
    }

    void readFromString(const std::string& s) {
        is_neg = false;
        limbs.clear();

        size_t pos = 0;
        while (pos < s.size() && std::isspace(static_cast<unsigned char>(s[pos]))) {
            ++pos;
        }

        if (pos == s.size()) {
            throw std::invalid_argument("empty string");
        }

        bool neg = false;
        if (s[pos] == '+' || s[pos] == '-') {
            neg = (s[pos] == '-');
            ++pos;
        }

        while (pos < s.size() && s[pos] == '0') {
            ++pos;
        }

        std::string digits;
        while (pos < s.size() && !std::isspace(static_cast<unsigned char>(s[pos]))) {
            if (!std::isdigit(static_cast<unsigned char>(s[pos]))) {
                throw std::invalid_argument("invalid character in integer string");
            }
            digits.push_back(s[pos]);
            ++pos;
        }

        while (pos < s.size()) {
            if (!std::isspace(static_cast<unsigned char>(s[pos]))) {
                throw std::invalid_argument("invalid trailing characters");
            }
            ++pos;
        }

        if (digits.empty()) {
            limbs = {0};
            is_neg = false;
            return;
        }

        for (int i = static_cast<int>(digits.size()); i > 0; i -= BASE_DIGITS) {
            int start = std::max(0, i - BASE_DIGITS);
            int len = i - start;
            uint32_t block = static_cast<uint32_t>(std::stoul(digits.substr(start, len)));
            limbs.push_back(block);
        }

        is_neg = neg;
        normalize();
    }

public:
    BigInt() : is_neg(false), limbs{0} {}

    BigInt(long long value) {
        long long x = value;
        is_neg = (x < 0);

        limbs.clear();

        // 处理 LLONG_MIN 风险：转成无符号绝对值
        unsigned long long ux;
        if (x < 0) {
            ux = static_cast<unsigned long long>(-(x + 1)) + 1ULL;
        } else {
            ux = static_cast<unsigned long long>(x);
        }

        if (ux == 0) {
            limbs.push_back(0);
            is_neg = false;
            return;
        }

        while (ux > 0) {
            limbs.push_back(static_cast<uint32_t>(ux % BASE));
            ux /= BASE;
        }

        normalize();
    }

    explicit BigInt(const std::string& s) {
        readFromString(s);
    }

    static BigInt abs(const BigInt& x) {
        return x.abs();
    }

    BigInt abs() const {
        BigInt t = *this;
        t.is_neg = false;
        return t;
    }

    std::string toString() const {
        if (isZero()) return "0";

        std::string s = is_neg ? "-" : "";
        s += std::to_string(limbs.back());

        for (int i = static_cast<int>(limbs.size()) - 2; i >= 0; --i) {
            std::string part = std::to_string(limbs[i]);
            s += std::string(BASE_DIGITS - part.length(), '0') + part;
        }

        return s;
    }

    friend std::ostream& operator<<(std::ostream& os, const BigInt& x) {
        os << x.toString();
        return os;
    }

    friend std::istream& operator>>(std::istream& is, BigInt& x) {
        std::string s;
        is >> s;
        x.readFromString(s);
        return is;
    }

    friend bool operator==(const BigInt& a, const BigInt& b) {
        return a.is_neg == b.is_neg && a.limbs == b.limbs;
    }

    friend bool operator!=(const BigInt& a, const BigInt& b) {
        return !(a == b);
    }

    friend bool operator<(const BigInt& a, const BigInt& b) {
        if (a.is_neg != b.is_neg) {
            return a.is_neg;
        }

        int cmp = compareAbs(a, b);
        if (!a.is_neg) {
            return cmp < 0;
        } else {
            return cmp > 0;
        }
    }

    friend bool operator<=(const BigInt& a, const BigInt& b) {
        return !(b < a);
    }

    friend bool operator>(const BigInt& a, const BigInt& b) {
        return b < a;
    }

    friend bool operator>=(const BigInt& a, const BigInt& b) {
        return !(a < b);
    }

    BigInt operator-() const {
        BigInt res = *this;
        if (!res.isZero()) {
            res.is_neg = !res.is_neg;
        }
        return res;
    }

    BigInt operator+() const {
        return *this;
    }

    friend BigInt operator+(const BigInt& a, const BigInt& b) {
        if (a.is_neg == b.is_neg) {
            BigInt res = addAbs(a, b);
            res.is_neg = a.is_neg;
            res.normalize();
            return res;
        }

        int cmp = compareAbs(a, b);
        if (cmp == 0) {
            return BigInt(0);
        }

        if (cmp > 0) {
            BigInt res = subAbs(a, b);
            res.is_neg = a.is_neg;
            res.normalize();
            return res;
        } else {
            BigInt res = subAbs(b, a);
            res.is_neg = b.is_neg;
            res.normalize();
            return res;
        }
    }

    friend BigInt operator-(const BigInt& a, const BigInt& b) {
        return a + (-b);
    }

    friend BigInt operator*(const BigInt& a, const BigInt& b) {
        if (a.isZero() || b.isZero()) {
            return BigInt(0);
        }
        BigInt res = mulAbs(a, b);
        res.is_neg = (a.is_neg != b.is_neg);
        res.normalize();
        return res;
    }

    friend BigInt operator/(const BigInt& a, const BigInt& b) {
        if (b.isZero()) {
            throw std::runtime_error("division by zero");
        }
        if (a.isZero()) {
            return BigInt(0);
        }

        auto [q, r] = divmodAbs(a.abs(), b.abs());
        q.is_neg = (a.is_neg != b.is_neg) && !q.isZero();
        q.normalize();
        return q;
    }

    friend BigInt operator%(const BigInt& a, const BigInt& b) {
        if (b.isZero()) {
            throw std::runtime_error("modulo by zero");
        }
        if (a.isZero()) {
            return BigInt(0);
        }

        auto [q, r] = divmodAbs(a.abs(), b.abs());
        (void)q;
        r.is_neg = a.is_neg && !r.isZero(); // 与 C++ 内建整数保持一致：余数跟被除数同号
        r.normalize();
        return r;
    }

    BigInt& operator+=(const BigInt& other) {
        *this = *this + other;
        return *this;
    }

    BigInt& operator-=(const BigInt& other) {
        *this = *this - other;
        return *this;
    }

    BigInt& operator*=(const BigInt& other) {
        *this = *this * other;
        return *this;
    }

    BigInt& operator/=(const BigInt& other) {
        *this = *this / other;
        return *this;
    }

    BigInt& operator%=(const BigInt& other) {
        *this = *this % other;
        return *this;
    }

    BigInt& operator++() {
        *this += BigInt(1);
        return *this;
    }

    BigInt operator++(int) {
        BigInt tmp = *this;
        ++(*this);
        return tmp;
    }

    BigInt& operator--() {
        *this -= BigInt(1);
        return *this;
    }

    BigInt operator--(int) {
        BigInt tmp = *this;
        --(*this);
        return tmp;
    }
};

// ===================== 测试示例 =====================
int main() {
    BigInt a("123456789123456789123456789");
    BigInt b("-99999999999999999999999999");
    BigInt c("123456789");
    BigInt d("-1000");

    std::cout << "a = " << a << "\n";
    std::cout << "b = " << b << "\n";
    std::cout << "c = " << c << "\n";
    std::cout << "d = " << d << "\n\n";

    std::cout << "a + b = " << (a + b) << "\n";
    std::cout << "a - b = " << (a - b) << "\n";
    std::cout << "a * c = " << (a * c) << "\n";
    std::cout << "a / c = " << (a / c) << "\n";
    std::cout << "a % c = " << (a % c) << "\n";
    std::cout << "b / d = " << (b / d) << "\n";
    std::cout << "b % d = " << (b % d) << "\n\n";

    BigInt x, y;
    std::cout << "请输入两个大整数: ";
    std::cin >> x >> y;
    std::cout << "x + y = " << (x + y) << "\n";
    std::cout << "x - y = " << (x - y) << "\n";
    std::cout << "x * y = " << (x * y) << "\n";
    if (y != BigInt(0)) {
        std::cout << "x / y = " << (x / y) << "\n";
        std::cout << "x % y = " << (x % y) << "\n";
    } else {
        std::cout << "y 为 0，无法做除法和取模。\n";
    }

    return 0;
}