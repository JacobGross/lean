/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE

  Author: Lev Nachmanson
*/

#pragma once
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <vector>
#include <set>
#include <utility>
#include "util/lp/binary_heap_priority_queue.h"
#include "util/lp/hash_helper.h"

typedef std::pair<unsigned, unsigned> upair;

namespace lean {
template <typename  T>
class binary_heap_upair_queue {
    binary_heap_priority_queue<T> m_q;
    std::unordered_map<upair, unsigned> m_pairs_to_index;
    std::vector<upair> m_pairs; // inverse to index
    std::vector<unsigned> m_available_spots;
public:
    binary_heap_upair_queue(unsigned size);

    unsigned dequeue_available_spot();
    bool is_empty() const { return m_q.is_empty(); }

    unsigned size() const {return m_q.size(); }

    bool contains(unsigned i, unsigned j) const { return m_pairs_to_index.find(std::make_pair(i, j)) != m_pairs_to_index.end();
    }

    void remove(unsigned i, unsigned j);
    bool ij_index_is_new(unsigned ij_index) const;
    void enqueue(unsigned i, unsigned j, const T & priority);
    void dequeue(unsigned & i, unsigned &j);
    T get_priority(unsigned i, unsigned j) const;
#ifdef LEAN_DEBUG
    bool pair_to_index_is_a_bijection() const;
    bool available_spots_are_correct() const;
    bool is_correct() const {
        return m_q.is_consistent() && pair_to_index_is_a_bijection() && available_spots_are_correct();
    }
#endif
};
}
