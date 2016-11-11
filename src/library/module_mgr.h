/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include <utility>
#include <vector>
#include <util/name.h>
#include <kernel/environment.h>
#include <util/task_queue.h>
#include <unordered_map>
#include "frontends/lean/parser.h"
#include "util/period.h"
#include "library/messages.h"
#include "library/io_state.h"
#include "library/trace.h"

namespace lean {

typedef std::string module_id;

enum class module_src {
    OLEAN,
    LEAN,
};

struct unit {};

struct module_info {
    module_id m_mod;
    module_src m_source = module_src::LEAN;
    time_t m_mtime = -1, m_trans_mtime = -1;
    std::vector<std::pair<module_id, module_name>> m_deps;
    optional<std::string> m_lean_contents;

    period m_version = 0;

    struct parse_result {
        optional<environment> m_env;
        name_map<delayed_theorem> m_delayed_theorems;
        std::string m_obj_code;
        bool m_ok = false;
        snapshot_vector m_snapshots;
    };

    task_result<parse_result> m_result;
    snapshot_vector m_still_valid_snapshots;

    task_result<unit> m_olean_task;
};

class module_vfs {
public:
    virtual ~module_vfs() {}
    // need to support changed lean dependencies of olean files
    // need to support changed editor dependencies of olean files
    virtual std::tuple<std::string, module_src, time_t> load_module(module_id const &, bool can_use_olean) = 0;
};

class fs_module_vfs : public module_vfs {
public:
    std::unordered_set<module_id> m_modules_to_load_from_source;
    std::tuple<std::string, module_src, time_t> load_module(module_id const & id, bool can_use_olean) override;
};

class module_mgr {
    period m_current_period = 1;

    bool m_use_snapshots = false;
    bool m_save_olean = false;

    environment m_initial_env;
    io_state m_ios;
    module_vfs * m_vfs;
    message_buffer * m_msg_buf;

    mutex m_mutex;
    std::unordered_map<module_id, module_info> m_modules;

    void rebuild_rdeps(module_id const & id);
    void build_module(module_id const & id, bool can_use_olean, name_set module_stack);
    std::vector<module_name> get_direct_imports(module_id const &id, std::string const &contents);
    void gather_transitive_imports(
        std::vector<std::tuple<module_id, module_name, module_info>> & res,
        std::unordered_set<module_id> & visited,
        module_id const & id, module_name const & import);
    std::vector<std::tuple<module_id, module_name, module_info>> gather_transitive_imports(
            module_id const & id, std::vector<module_name> const & imports);
    bool get_snapshots_or_unchanged_module(
            module_id const & id, std::string const & contents, time_t mtime, snapshot_vector &vector);

public:
    module_mgr(module_vfs * vfs, message_buffer * msg_buf, environment const & initial_env, io_state const & ios) :
            m_initial_env(initial_env), m_ios(ios), m_vfs(vfs), m_msg_buf(msg_buf) {}

    std::unordered_set<module_id> m_roi;

    message_buffer * get_msg_buf() const { return m_msg_buf; }

    bool is_in_roi(module_id const &, optional<pos_info> const &);

    void invalidate(module_id const & id);

    module_info get_module(module_id const &);

    snapshot_vector get_snapshots(module_id const & id);

    void set_use_snapshots(bool use_snapshots) { m_use_snapshots = use_snapshots; }
    bool get_use_snapshots() const { return m_use_snapshots; }

    void set_save_olean(bool save_olean) { m_save_olean = save_olean; }
    bool get_save_olean() const { return m_save_olean; }

    environment get_initial_env() const { return m_initial_env; }
    options get_options() const { return m_ios.get_options(); }
    io_state get_io_state() const { return m_ios; }
};

module_mgr * get_global_module_mgr();
module_id const & get_global_module_id();
class scoped_module_mgr {
    scoped_module_mgr * m_old;
public:
    module_mgr * m_mgr;
    module_id m_mod;

    scoped_module_mgr(module_mgr *, module_id const &);
    ~scoped_module_mgr();
};

template <class T>
class module_task : public task<T> {
    module_mgr * m_mod_mgr;
    module_id m_mod;
    message_bucket_id m_bucket;
    optional<pos_info> m_pos;
    task_priority m_roi_prio;

public:
    module_task(task_priority const & def_prio, task_priority const & roi_prio, optional<pos_info> const & pos) :
            task<T>(get_global_module_mgr()->is_in_roi(get_global_module_id(), pos) ? roi_prio : def_prio),
            m_mod_mgr(get_global_module_mgr()),
            m_mod(get_global_module_id()),
            m_bucket(get_scope_message_context().new_sub_bucket()),
            m_pos(pos), m_roi_prio(roi_prio) {}

    virtual T execute_core() = 0;

    T execute() final override;

    module_id get_module() const { return m_mod; }
    period get_version() const { return m_bucket.m_version; }
    pos_info get_pos_or_something() const { return m_pos ? *m_pos : pos_info{1, 0}; }
};

template <class T>
T module_task<T>::execute() {
    scoped_module_mgr scoped_mod_mgr(m_mod_mgr, m_mod);
    io_state ios = m_mod_mgr->get_io_state();
    scope_global_ios scoped_ios(ios);
    scoped_message_buffer scoped_msg_buf(m_mod_mgr->get_msg_buf());
    scope_message_context scope_msg_ctx(m_bucket);
    try {
        scope_traces_as_messages scope_traces(get_module(), get_pos_or_something());
        return execute_core();
    } catch (throwable & ex) {
        environment env;
        message_builder builder(m_mod_mgr->get_initial_env(), m_mod_mgr->get_io_state(), get_module(),
                                get_pos_or_something(), ERROR);
        // builder << "Exception during task: " << this->description() << "\n";
        builder.set_exception(ex);
        builder.report();
        throw;
    }
}

}
