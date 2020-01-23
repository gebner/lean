#include "util/name.h"
#include "library/type_context.h"
#include "kernel/expr_maps.h"
#include <functional>
#include <unordered_set>
#include <unordered_map>
#include "util/name_hash_set.h"

namespace lean {

struct feature {
    feature(name const & n) : m_name(n) {}
    feature(name const & n, name const & p) : m_name(n), m_parent(p) {}

    name m_name;
    optional<name> m_parent;

    bool operator==(feature const & that) const noexcept {
        return m_name == that.m_name && m_parent == that.m_parent;
    }
};

}

template <> struct std::hash<lean::feature> {
    std::size_t operator()(lean::feature const & f) const noexcept {
        return f.m_name.hash() ^ (16777619 * (f.m_parent ? f.m_parent->hash() : 0));
    }
};

namespace lean {

using feature_vec = std::vector<feature>;

feature_vec isect(feature_vec const & a, feature_vec const & b);
feature_vec union_(feature_vec const & a, feature_vec const & b);

struct feature_collector {
    type_context_old & m_ctx;

    name_hash_set m_ignored_consts;
    name_hash_set m_ignored_preds;

    feature_vec operator()(expr const & thm);

    feature_collector(type_context_old & ctx);

    friend struct collect_visitor;
};

feature_vec feature_vec_of(type_context_old & ctx, expr const & e);

struct feature_stats {
    unsigned m_thms;
    std::unordered_map<feature, unsigned> m_feature_counts;

    void add(feature_vec const & fv);

    float idf(feature const & f) const;

    float norm(feature_vec const & f) const;

    float dotp(feature_vec const & a, feature_vec const & b) const;

    float cosine_similarity(feature_vec const & a, feature_vec const & b) const;
};

class vm_obj;
vm_obj to_obj(feature const & f);
feature to_feature(vm_obj const & o);
vm_obj to_obj(feature_vec const & feat_vec);
feature_vec const & to_feature_vec(vm_obj const & o);

void initialize_feature_search();
void finalize_feature_search();

}