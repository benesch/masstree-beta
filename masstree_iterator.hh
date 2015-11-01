/* Masstree
 * Eddie Kohler, Yandong Mao, Robert Morris
 * Copyright (c) 2012-2014 President and Fellows of Harvard College
 * Copyright (c) 2012-2014 Massachusetts Institute of Technology
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, subject to the conditions
 * listed in the Masstree LICENSE file. These conditions include: you must
 * preserve this copyright notice, and you cannot mention the copyright
 * holders in advertising related to the Software without their permission.
 * The Software is provided WITHOUT ANY WARRANTY, EXPRESS OR IMPLIED. This
 * notice is a summary of the Masstree LICENSE file; the license in that file
 * is legally binding.
 */
#ifndef MASSTREE_ITERATOR_HH
#define MASSTREE_ITERATOR_HH
#include "masstree_scan.hh"

namespace Masstree {
template <typename P>
class basic_table<P>::iterator
    : std::iterator<std::forward_iterator_tag, itvalue_type> {
    typedef typename P::ikey_type ikey_type;
    typedef typename node_type::key_type key_type;
    typedef typename node_type::leaf_type::leafvalue_type leafvalue_type;
    typedef typename node_type::nodeversion_type nodeversion_type;
    typedef typename leaf_type::permuter_type permuter_type;
    typedef typename leaf_type::bound_type bound_type;

  public:
    iterator(basic_table<P>* table, threadinfo* ti, Str firstkey = "");
    static iterator make_end(basic_table<P>* table, threadinfo *ti);

    itvalue_type& operator*() { return pair_; };
    itvalue_type* operator->() { return &pair_; };
    bool operator==(iterator& rhs) { return (end_ == rhs.end_) && (end_ || ka_.compare(rhs.ka_) == 0); };
    bool operator!=(iterator& rhs) { return !(*this == rhs); };
    bool operator<(iterator& rhs) { return (!end_ && rhs.end_) || ka_.compare(rhs.ka_) < 0; };
    bool operator<=(iterator& rhs) { return *this < rhs || *this == rhs; };
    iterator operator++() { advance(); return *this; };
    iterator operator++(int) { iterator it = *this; advance(); return it; };

  private:
    basic_table<P>* table_;
    threadinfo* ti_;
    key_type ka_;
    itvalue_type pair_;
    bool emit_equal_;
    bool end_;
    union {
        ikey_type x[(MASSTREE_MAXKEYLEN + sizeof(ikey_type) - 1)/sizeof(ikey_type)];
        char s[MASSTREE_MAXKEYLEN];
    } keybuf_;

    void advance(bool allow_next = true);


    // Debugging support.
    int id_;
    static int count_;

    void dprintf(const char *format, ...) {
        va_list args;
        va_start(args, format);
        fprintf(stderr, "it%d: ", id_);
        vfprintf(stderr, format, args);
        va_end(args);
    }
};

template <typename P> int basic_table<P>::iterator::count_ = 0;

template <typename P>
basic_table<P>::iterator::iterator(basic_table<P>* table, threadinfo* ti, Str firstkey)
    : table_(table), ti_(ti), emit_equal_(true), end_(false), id_(count_++) {
    masstree_precondition(firstkey.len <= (int) sizeof(keybuf_));
    memcpy(keybuf_.s, firstkey.s, firstkey.len);
    ka_ = key_type(keybuf_.s, firstkey.len);

    advance();
};

template <typename P>
typename basic_table<P>::iterator
basic_table<P>::iterator::make_end(basic_table<P>* table, threadinfo *ti) {
    iterator it = iterator(table, ti);
    it.end_ = true;
    return it;
}

template <typename P>
void
basic_table<P>::iterator::advance(bool allow_next) {
    key_indexed_position kx;
    int keylenx;
    char suffixbuf[MASSTREE_MAXKEYLEN];
    Str suffix;
    leafvalue_type entry;
    leaf_type* n;
    nodeversion_type v;
    permuter_type perm;
    bool found = false;
    node_type* root;

 retry:
    keylenx = 0;
    root = table_->root();
    ka_.unshift_all();

    // Find initial.
    // XXX The control flow of this loop is incomprehensible.
    while (!found) {
        n = root->reach_leaf(ka_, v, *ti_);

        if (v.deleted())
            goto retry;
        n->prefetch();
        perm = n->permutation();

        kx = bound_type::lower(ka_, *n);
        if (kx.p >= 0) {
            keylenx = n->keylenx_[kx.p];
            fence();
            entry = n->lv_[kx.p];
            entry.prefetch(keylenx);
            if (n->keylenx_has_ksuf(keylenx)) {
                suffix = n->ksuf(kx.p);
                memcpy(suffixbuf, suffix.s, suffix.len);
                suffix.s = suffixbuf;
            }
        }
        if (n->has_changed(v)) {
            ti_->mark(tc_leaf_retry);
            n = n->advance_to_key(ka_, v, *ti_);
            goto retry;
        }

        if (kx.p >= 0) {
            if (n->keylenx_is_layer(keylenx)) {
                root = entry.layer();
                ka_.shift();
                continue;
            } else if (n->keylenx_has_ksuf(keylenx)) {
                int ksuf_compare = suffix.compare(ka_.suffix());
                if (ksuf_compare > 0 || (ksuf_compare == 0 && emit_equal_)) {
                    int keylen = ka_.assign_store_suffix(suffix);
                    ka_.assign_store_length(keylen);
                    found = true;
                }
            }
            found = emit_equal_;
        }
        break;
    }

    // Find next.
    int kp;
    int ki = kx.i + 1;
    while (!found) {
        if (v.deleted())
            goto retry;

        kp = unsigned(ki) < unsigned(perm.size()) ? perm[ki] : -1;
        if (kp >= 0) {
            ikey_type ikey = n->ikey0_[kp];
            int keylenx = n->keylenx_[kp];
            int keylen = keylenx;
            fence();
            entry = n->lv_[kp];
            entry.prefetch(keylenx);
            if (n->keylenx_has_ksuf(keylenx))
                keylen = ka_.assign_store_suffix(n->ksuf(kp));

            if (n->has_changed(v))
                goto retry;
            else if (ka_.compare(ikey, keylenx) >= 0) {
                ki++;
                continue;
            }

            ka_.assign_store_ikey(ikey);
            if (n->keylenx_is_layer(keylenx)) {
                root = entry.layer();
                n = root->reach_leaf(ka_, v, *ti_);
                ka_.shift();
                goto changed;
            } else {
                ka_.assign_store_length(keylen);
                found = true;
                break;
            }
        }

        if (!n->has_changed(v)) {
            n = n->safe_next();
            if (!n) {
                if (allow_next) {
                    ka_.unshift();
                    ka_.increment();
                    emit_equal_ = true;
                    advance(false);
                    return;
                } else {
                    end_ = true;
                    return;
                }
            }
        }

     changed:
        n->prefetch();
        v = n->stable();
        perm = n->permutation();
        ki = bound_type::lower(ka_, *n).i;
    }

    pair_ = itvalue_type(ka_, entry.value());
    emit_equal_ = false;
}

template <typename P>
typename basic_table<P>::iterator
basic_table<P>::begin(threadinfo& ti) {
    return iterator(this, &ti);
}

template <typename P>
typename basic_table<P>::iterator
basic_table<P>::end(threadinfo& ti) {
    return iterator::make_end(this, &ti);
}

template <typename P>
typename basic_table<P>::iterator
basic_table<P>::iterate_from(Str firstkey, threadinfo& ti) {
    return iterator(this, &ti, firstkey);
}
}
#endif
