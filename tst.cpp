// Copyright (c) 2013 Bryce Adelstein-Lelbach
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)

#include <iostream>
#include <algorithm>

#include <boost/assert.hpp>
#include <boost/cstdint.hpp>

#include "tst.hpp"

#define requires(...)

#define WeightType(C) weight_type<C>::type

template <typename C>
struct weight_type
{
    typedef boost::uint64_t type;
};

template <typename T>
T maximum(T a, T b, T c)
{
    return (std::max)(a, (std::max)(b, c));
}

boost::uint64_t successor(boost::uint64_t i)
{
    return i + 1;
}

template <typename Char, typename T>
bool empty(tst_node<Char, T> t)
{
    return !(t.lt || t.eq || t.gt);
}

template <typename Char, typename T>
bool has_left_successor(tst_node<Char, T> t)
{
    return t.lt;
}

template <typename Char, typename T>
bool has_middle_successor(tst_node<Char, T> t)
{
    return t.eq;
}

template <typename Char, typename T>
bool has_right_successor(tst_node<Char, T> t)
{
    return t.gt;
}

template <typename Char, typename T>
tst_node<Char, T> left_successor(tst_node<Char, T> t)
{
    BOOST_ASSERT(t.lt);
    return *t.lt;
}

template <typename Char, typename T>
tst_node<Char, T> middle_successor(tst_node<Char, T> t)
{
    BOOST_ASSERT(t.eq);
    return *t.eq;
}

template <typename Char, typename T>
tst_node<Char, T> right_successor(tst_node<Char, T> t)
{
    BOOST_ASSERT(t.gt);
    return *t.gt;
}

enum visit { pre, in_left, in_middle, post };

std::ostream& operator<<(std::ostream& os, visit v)
{
    switch (v)
    {
        case pre:       os << "pre";       break; 
        case in_left:   os << "in_left";   break; 
        case in_middle: os << "in_middle"; break; 
        case post:      os << "post";      break; 

        default: BOOST_ASSERT(false); break; 
    }
    return os;
}

template <typename Char, typename T>
bool has_predecessor(tst_node<Char, T> t)
{
    return t.parent;
}

template <typename Char, typename T>
tst_node<Char, T> predecessor(tst_node<Char, T> t)
{
    BOOST_ASSERT(t.parent);
    return *t.parent;
}

///////////////////////////////////////////////////////////////////////////////
template <typename C>
    requires(TrifurcateCoordinate(C))
typename WeightType(C) weight_recursive(C c)
{
    // Precondition: ternary_tree(c)
    typedef typename WeightType(C) N;
    if (empty(c)) return N(0);
    N l(0);
    N m(0);
    N r(0);
    if (has_left_successor(c))
        l = weight_recursive(left_successor(c));
    if (has_middle_successor(c))
        m = weight_recursive(middle_successor(c));
    if (has_right_successor(c))
        r = weight_recursive(right_successor(c));
    return successor(l + m + r);
}

template <typename C>
    requires(TrifurcateCoordinate(C))
typename WeightType(C) height_recursive(C c)
{
    // Precondition: ternary_tree(c)
    typedef typename WeightType(C) N;
    if (empty(c)) return N(0);
    N l(0);
    N m(0);
    N r(0);
    if (has_left_successor(c))
        l = height_recursive(left_successor(c));
    if (has_middle_successor(c))
        m = height_recursive(middle_successor(c));
    if (has_right_successor(c))
        r = height_recursive(right_successor(c));
    return successor(maximum(l, m, r));
}

template <typename C, typename Proc>
    requires(TrifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 2 &&
        visit == InputType(Proc, 0) &&
        C == InputType(Proc, 1))
Proc traverse_nonempty(C c, Proc proc)
{
    // Precondition: ternary_tree(c) && !empty(c)
    proc(pre, c);
    if (has_left_successor(c))
        proc = traverse_nonempty(left_successor(c), proc);
    proc(in_left, c);
    if (has_middle_successor(c))
        proc = traverse_nonempty(middle_successor(c), proc);
    proc(in_middle, c);
    if (has_right_successor(c))
        proc = traverse_nonempty(right_successor(c), proc);
    proc(post, c);
    return proc;
}

template <typename T>
    requires(TridirectionalTrifurcateCoordinate(T))
bool is_left_successor(T j)
{
    // Precondition: has_predecessor(j)
    T i = predecessor(j);
    return has_left_successor(i) && left_successor(i) == j;
}

template <typename T>
    requires(TridirectionalTrifurcateCoordinate(T))
bool is_middle_successor(T j)
{
    // Precondition: has_predecessor(j)
    T i = predecessor(j);
    return has_middle_successor(i) && middle_successor(i) == j;
}

template <typename T>
    requires(TridirectionalTrifurcateCoordinate(T))
bool is_right_successor(T j)
{
    // Precondition: has_predecessor(j)
    T i = predecessor(j);
    return has_right_successor(i) && right_successor(i) == j;
}

///////////////////////////////////////////////////////////////////////////////

struct print_traverser
{
    print_traverser
    operator()(visit v, tst_node<char, boost::uint64_t> t) const
    {
        std::cout << "'" << t.id << "' " << v << "\n";
        return *this;
    };
};

struct is_successor_traverser
{
    is_successor_traverser
    operator()(visit v, tst_node<char, boost::uint64_t> t) const
    {
        if (pre == v)
        {
            if (has_predecessor(t))
                std::cout << "'" << t.id << "' | "
                          << is_left_successor(t) << " | "
                          << is_middle_successor(t) << " | "
                          << is_right_successor(t) << " |\n";
            else // root node
                std::cout << "'" << t.id << "' |   |   |   |\n";
        }
        return *this;
    };
};

int main()
{
    std::string abc("abc"), def("def"), abcdef("abcdef");

    tst<char, boost::uint64_t> t;

    t.add(abc.begin(), abc.end(), 17);
    t.add(def.begin(), def.end(), 42);
    t.add(abcdef.begin(), abcdef.end(), 9); 

    std::string::iterator it = abc.begin();
    boost::uint64_t* val = t.find(it, abc.end());
    BOOST_ASSERT(val);
    BOOST_ASSERT(17 == *val);

    it = def.begin();
    val = t.find(it, abc.end());
    BOOST_ASSERT(val);
    BOOST_ASSERT(42 == *val);

    it = abcdef.begin();
    val = t.find(it, abc.end());
    BOOST_ASSERT(val);
    BOOST_ASSERT(9 == *val);

    std::cout << "Weight of {\"abc\":17, \"def\":42, \"abcdef\":9} == "
              << weight_recursive(*t.root)
              << "\n";

    std::cout << "Height of {\"abc\":17, \"def\":42, \"abcdef\":9} == "
              << height_recursive(*t.root)
              << "\n";

    std::cout << "\nTraversal\n";

    traverse_nonempty(*t.root, print_traverser());

    std::cout << "\nIs the node a left (l), middle (m) or right (r) successor\n"
              << "    | l | m | r |\n";

    traverse_nonempty(*t.root, is_successor_traverser());
}

