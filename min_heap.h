#ifndef SATSOLVER_MIN_HEAP_H
#define SATSOLVER_MIN_HEAP_H

#include "debug.h"
#include <vector>
#include <unordered_map>

template <typename Key, typename Compare>
class min_heap {
    std::vector<Key> heap;
    std::unordered_map<Key, int> indices;
    Compare comparator;

    static int left_child(int i) { return 2 * i + 1; }
    static int right_child(int i) { return 2 * i + 2; }
    static int parent(int i) { return (i - 1) / 2; }

    void sift_down(int i) {
        auto x = heap[i];
        while (left_child(i) < heap.size()) {
            auto j = left_child(i);
            if (right_child(i) < heap.size() && comparator(heap[right_child(i)], heap[left_child(i)])) {
                j = right_child(i);
            }
            if (comparator(x, heap[j]))
                break;

            heap[i] = heap[j];
            indices[heap[i]] = i;
            i = j;
        }
        heap[i] = x;
        indices[x] = i;
    }

    void sift_up(int i) {
        auto x = heap[i];
        auto p = parent(i);
        while (i != 0 && comparator(x, heap[p])) {
            heap[i] = heap[p];
            indices[heap[p]] = i;
            i = p;
            p = parent(p);
        }
        heap[i] = x;
        indices[x] = i;
    }

public:
    explicit min_heap(const Compare& comparator) : comparator(comparator) {}

    void rebuild_heap(const std::vector<Key> container) {
        heap = container;
        indices.clear();
        for (auto i = (int) heap.size() / 2; i >= 0; i--) {
            sift_down(i);
        }
        for (auto i = 0; i < heap.size(); i++) {
            indices[heap[i]] = i;
        }
    }

    size_t size() const {
        return heap.size();
    }

    bool in_heap(const Key& key) const {
        return indices.find(key) != indices.end();
    }

    void decrease(const Key& key) {
        if (!in_heap(key))
            return;

        sift_up(indices[key]);
    }

    void increase(const Key& key) {
        if (!in_heap(key))
            return;

        sift_down(indices[key]);
    }

    Key min() const {
        debug(if (heap.empty())
            debug_logic_error("min from empty heap"))

        return heap[0];
    }

    Key extract_min() {
        debug(if (heap.empty())
            debug_logic_error("extract_min from empty heap"))

        auto key = heap[0];
        heap[0] = heap[heap.size() - 1];
        indices[heap[0]] = 0;
        indices.erase(key);
        heap.pop_back();
        if (heap.size() > 1)
            sift_down(0);
        return key;
    }

    void insert(const Key& key) {
        if (in_heap(key))
            debug_logic_error("Insert duplicate key: " << key)

        indices[key] = heap.size();
        heap.push_back(key);
        sift_up(indices[key]);
    }

    void remove(const Key& key) {
        if (!in_heap(key))
            debug_logic_error("Remove missing key: " << key)

        int key_index = indices[key];
        indices.erase(key);
        if (key_index == heap.size() - 1) {
            heap.pop_back();
        } else {
            heap[key_index] = heap[heap.size() - 1];
            indices[heap[key_index]] = key_index;
            heap.pop_back();
            sift_down(key_index);
        }
    }
};


#endif //SATSOLVER_MIN_HEAP_H