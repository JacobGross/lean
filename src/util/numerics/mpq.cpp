/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/sstream.h"
#include "util/thread.h"
#include "util/numerics/mpq.h"
#include "util/numerics/mpbq.h"

namespace lean {
mpq * numeric_traits<mpq>::pi_l = nullptr;
mpq * numeric_traits<mpq>::pi_n = nullptr;
mpq * numeric_traits<mpq>::pi_u = nullptr;

void numeric_traits<mpq>::initialize() {
    pi_l = new mpq((3373259426.0 + 273688.0 / (1<<21)) / (1<<30));
    pi_n = new mpq((3373259426.0 + 273688.0 / (1<<21)) / (1<<30));
    pi_u = new mpq((3373259426.0 + 273688.0 / (1<<21)) / (1<<30));
}

void numeric_traits<mpq>::finalize() {
    delete pi_l;
    delete pi_n;
    delete pi_u;
}

mpq & mpq::operator=(mpbq const & b) {
    *this = 2;
    power(*this, *this, b.get_k());
    inv();
    *this *= b.get_numerator();
    return *this;
}

MK_THREAD_LOCAL_GET_DEF(mpz, get_tlocal1);
int cmp(mpq const & a, mpz const & b) {
    if (a.is_integer()) {
        return mpz_cmp(mpq_numref(a.m_val), mpq::zval(b));
    } else {
        mpz & tmp = get_tlocal1();
        mpz_mul(mpq::zval(tmp), mpq_denref(a.m_val), mpq::zval(b));
        return mpz_cmp(mpq_numref(a.m_val), mpq::zval(tmp));
    }
}

void mpq::floor() {
    if (is_integer())
        return;
    bool neg = is_neg();
    mpz_tdiv_q(mpq_numref(m_val), mpq_numref(m_val), mpq_denref(m_val));
    mpz_set_ui(mpq_denref(m_val), 1);
    if (neg)
        mpz_sub_ui(mpq_numref(m_val), mpq_numref(m_val), 1);
}

void mpq::ceil() {
    if (is_integer())
        return;
    bool pos = is_pos();
    mpz_tdiv_q(mpq_numref(m_val), mpq_numref(m_val), mpq_denref(m_val));
    mpz_set_ui(mpq_denref(m_val), 1);
    if (pos)
        mpz_add_ui(mpq_numref(m_val), mpq_numref(m_val), 1);
}

mpz floor(mpq const & a) {
    if (a.is_integer())
        return a.get_numerator();
    mpz r;
    mpz_tdiv_q(mpq::zval(r), mpq_numref(a.m_val), mpq_denref(a.m_val));
    if (a.is_neg())
        --r;
    return r;
}

mpz ceil(mpq const & a) {
    if (a.is_integer())
        return a.get_numerator();
    mpz r;
    mpz_tdiv_q(mpq::zval(r), mpq_numref(a.m_val), mpq_denref(a.m_val));
    if (a.is_pos())
        ++r;
    return r;
}

void power(mpq & a, mpq const & b, unsigned k) {
    mpz_pow_ui(mpq_numref(a.m_val), mpq_numref(b.m_val), k);
    mpz_pow_ui(mpq_denref(a.m_val), mpq_denref(b.m_val), k);
    mpq_canonicalize(a.m_val);
}

extern void display(std::ostream & out, __mpz_struct const * v);

std::ostream & operator<<(std::ostream & out, mpq const & v) {
    if (v.is_integer()) {
        display(out, mpq_numref(v.m_val));
    } else {
        display(out, mpq_numref(v.m_val));
        out << "/";
        display(out, mpq_denref(v.m_val));
    }
    return out;
}

void display_decimal(std::ostream & out, mpq const & a, unsigned prec) {
    mpz n1, d1, v1;
    numerator(n1, a);
    denominator(d1, a);
    if (a.is_neg()) {
        out << "-";
        n1.neg();
    }
    v1 = n1 / d1;
    out << v1;
    n1 = rem(n1, d1);
    if (n1.is_zero())
        return;
    out << ".";
    for (unsigned i = 0; i < prec; i++) {
        n1 *= 10;
        v1 = n1 / d1;
        lean_assert(v1 < 10);
        out << v1;
        n1 = rem(n1, d1);
        if (n1.is_zero())
            return;
    }
    out << "?";
}

static mpq * g_zero = nullptr;

mpq const & numeric_traits<mpq>::zero() {
    lean_assert(is_zero(*g_zero));
    return *g_zero;
}

static mpq * g_one = nullptr;
mpq const & numeric_traits<mpq>::one() {
    return *g_one;
}

serializer & operator<<(serializer & s, mpq const & n) {
    std::ostringstream out;
    out << n;
    s << out.str();
    return s;
}

void initialize_mpq() {
    g_zero = new mpq();
    g_one  = new mpq(1);
    numeric_traits<mpq>::initialize();
}

void finalize_mpq() {
    numeric_traits<mpq>::finalize();
    delete g_zero;
    delete g_one;
}

mpq read_mpq(deserializer & d) {
    return mpq(d.read_string().c_str());
}
}

void print(lean::mpq const & v) { std::cout << v << std::endl; }
