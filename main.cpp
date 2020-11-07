#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <stdexcept>
#include <chrono>

using namespace std;

bool is_number(const string& number) {
    if (number.empty()) {
        return false;
    }
    return all_of(number.begin(), number.end(), [&](char digit) {
        return digit >= '0' && digit <= '9';
    });
}

bool is_less(const vector<int>& first, const vector<int>& second) {
    if (second.size() > first.size()) {
        return true;
    }
    if (first.size() > second.size()) {
        return false;
    }
    for (int i = int(first.size() - 1); i >= 0; --i) {
        if (first[i] == second[i]) {
            continue;
        }
        return first[i] < second[i];
    }
    return false;
}

void copy(const vector<int>& source, vector<int>& destination) {
    destination = vector<int>(source.size());
    for (size_t i = 0; i < source.size(); ++i) {
        destination[i] = source[i];
    }
}

void multiply(vector<int>& u, int v) {
    int carry = 0;
    for (int& i : u) {
        int temp = i * v + carry;
        i = temp % 10;
        carry = temp / 10;
    }
    if (carry > 0) {
        u.push_back(carry);
    }
    while (u.size() > 1 && u.back() == 0) {
        u.pop_back();
    }
}

class BigInteger {
private:
    const int base = 10;

    vector<int> digits;

    explicit BigInteger(const vector<int>& digits) {
        copy(digits, this->digits);
    }

    explicit BigInteger(int value) {
        if (value < 0) {
            throw invalid_argument("Value is less than zero.");
        }
        digits = vector<int>();
        while (value > 0) {
            digits.push_back(value % base);
            value /= base;
        }
    }

public:
    explicit BigInteger(const string& number) {
        if (!is_number(number)) {
            string exceptionMessage = "Argument \"" + number + "\" is not a number.";
            throw invalid_argument(exceptionMessage);
        }
        int firstNotZero = 0;
        while (firstNotZero < number.size() - 1 && number[firstNotZero] == '0') {
            ++firstNotZero;
        }
        digits = vector<int>(number.size() - firstNotZero);
        for (int i = int(number.size() - 1); i >= firstNotZero; --i) {
            digits[number.size() - i - 1] = number[i] - '0';
        }
    }

    BigInteger() {
        digits = vector<int>(1, 0);
    }

    BigInteger& operator=(const BigInteger& other) {
        digits = other.digits;
        return *this;
    }

    BigInteger operator+(const BigInteger& other) {
        int maxLength = max(digits.size(), other.digits.size());
        vector<int> newDigits(maxLength);
        int k = 0, digitsSum;
        for (int i = 0; i < maxLength; ++i) {
            digitsSum = (i < digits.size() ? digits[i] : 0)
                        + (i < other.digits.size() ? other.digits[i] : 0)
                        + k;
            newDigits[i] = digitsSum % base;
            k = digitsSum / base;
        }
        if (k > 0) {
            newDigits.push_back(k);
        }
        return BigInteger(newDigits);
    }

    BigInteger operator-(BigInteger& other) {
        if (is_less(digits, other.digits)) {
            string first_number = this->to_string();
            string second_number = other.to_string();
            string exception_message = "При вычитании \"" + second_number +
                                       "\" из \"" + first_number + "\" получаем отрицательное число.";
            throw invalid_argument(exception_message);
        }
        int k = 0;
        vector<int> new_digits(digits.size());
        for (int i = 0; i < int(digits.size()); ++i) {
            new_digits[i] = digits[i] - (i < other.digits.size() ? other.digits[i] : 0) - k;
            k = new_digits[i] < 0;
            if (k) {
                new_digits[i] += base;
            }
        }
        for (int i = int(new_digits.size() - 1); i >= 1; --i) {
            if (new_digits[i] == 0) {
                new_digits.erase(new_digits.begin() + i);
            } else {
                break;
            }
        }
        return BigInteger(new_digits);
    }

    BigInteger operator*(const BigInteger& other) {
        int new_size = int(digits.size() + other.digits.size());
        vector<int> new_digits(new_size);
        for (int i = 0; i < digits.size(); ++i) {
            int k = 0;
            for (int j = 0; j < other.digits.size(); ++j) {
                int t = digits[i] * other.digits[j] + new_digits[i + j] + k;
                new_digits[i + j] = t % base;
                k = t / base;
            }
            if (k > 0) {
                new_digits[i + other.digits.size()] += k;
            }
        }
        for (int i = new_size - 1; i > 0; --i) {
            if (new_digits[i] == 0) {
                new_digits.erase(new_digits.begin() + i);
            }
            else {
                break;
            }
        }
        return BigInteger(new_digits);
    }

    BigInteger operator/(const BigInteger& other) {
        vector<int> u = digits;
        vector<int> v = other.digits;
        int n = int(v.size());
        int m = int(u.size()) - n;
        vector<int> q(m);
        int d = base / (v[n - 1] + 1);
        multiply(u, d);
        multiply(v, d);
        if (u.size() == m + n) {
            u.push_back(0);
        }
        for (int j = m; j >= 0; --j) {
            int numerator = u[j + n] * base + u[j + n - 1];
            int q_hat = numerator / base;
            int r_hat = numerator % base;
            if (q_hat == base || q_hat * v[n - 2] > base * r_hat + u[j + n - 2]) {
                --q_hat;
                r_hat += v[n - 1];
                if (r_hat < base && (q_hat == base || q_hat * v[n - 2] > base * r_hat + u[j + n - 2])) {
                    --q_hat;
                    r_hat += v[n - 1];
                }
            }
            vector<int> tmp_v = v;
            multiply(tmp_v, q_hat);
            vector<int> tmp_u(n + 1);
            for (int i = j; i <= j + n; ++i) {
                tmp_u[i - j] = u[i];
            }
            BigInteger subtraction(tmp_u);
            bool less = is_less(tmp_u, tmp_v);
            if (less) {
                BigInteger b(base);
                for (int i = 0; i < n; ++i) {
                    subtraction = subtraction * b;
                }
            }
            BigInteger big_integer_v(tmp_v);
            subtraction = subtraction - big_integer_v;
            for (int i = j; i <= j + n; ++i) {
                u[i] = tmp_u[i - j];
            }
            q[j] = q_hat;
            if (less) {
                --q[j];
                v.push_back(0);
                int carry = 0;
                for (int i = j; i <= j + n; ++i) {
                    int tmp = u[i] + v[i - n] + carry;
                    u[i] = tmp % base;
                    carry = tmp / base;
                }
                v.pop_back();
            }
        }
        return BigInteger(q);
    }

    string to_string() {
        string numbers;
        for (int i = int(digits.size() - 1); i >= 0; --i) {
            numbers += std::to_string(digits[i] + '0');
        }
        return numbers;
    }
};

int main() {
    setlocale(LC_ALL, "Russian");
    string first, second;
    while (true) {
        cout << "Введите 2 числа: ";
        cin >> first >> second;
        try {
            auto start = chrono::high_resolution_clock::now();
            BigInteger a(first), b(second);
            BigInteger c = a / b;
            auto end = chrono::high_resolution_clock::now();
            cout << c.to_string() << endl;
            cout << "Затраченное время: " << chrono::duration_cast<chrono::nanoseconds>(end - start).count() << " наносекунд." << endl;
        }
        catch (exception e) {
            cout << e.what() << endl;
        }
    }
}