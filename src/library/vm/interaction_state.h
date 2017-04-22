/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Sebastian Ullrich
*/
#pragma once
#include <algorithm>
#include "util/sstream.h"
#include "kernel/environment.h"
#include "library/metavar_context.h"
#include "library/type_context.h"
#include "library/defeq_canonizer.h"
#include "kernel/scope_pos_info_provider.h"
#include "util/fresh_name.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/type_checker.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/pp_options.h"
#include "library/trace.h"
#include "library/util.h"
#include "library/cache_helper.h"
#include "library/module.h"
#include "library/documentation.h"
#include "library/scoped_ext.h"
#include "library/aux_definition.h"
#include "library/unfold_macros.h"
#include "library/message_builder.h"
#include "library/vm/vm.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_exceptional.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_string.h"
#include "library/vm/vm_options.h"
#include "library/vm/vm_name.h"
#include "library/vm/vm_nat.h"
#include "library/vm/vm_level.h"
#include "library/vm/vm_declaration.h"
#include "library/vm/vm_expr.h"
#include "library/vm/vm_list.h"
#include "library/vm/vm_option.h"
#include "library/compiler/vm_compiler.h"
#include "library/profiling.h"

namespace lean {

template <class State>
struct interaction_monad {
    struct vm_State : public vm_external {
        State m_val;

        vm_State(State const & v) : m_val(v) {}

        virtual ~vm_State() {}

        virtual void dealloc() override {
            this->~vm_State();
            get_vm_allocator().deallocate(sizeof(vm_State), this);
        }

        virtual vm_external * ts_clone(vm_clone_fn const &) override { return new vm_State(m_val); }

        virtual vm_external * clone(vm_clone_fn const &) override {
            return new(get_vm_allocator().allocate(sizeof(vm_State))) vm_State(m_val);
        }
    };

    static bool is_state(vm_obj const & o) {
        return is_external(o) && dynamic_cast<vm_State *>(to_external(o));
    }

    static State const & to_state(vm_obj const & o) {
        lean_vm_check(dynamic_cast<vm_State*>(to_external(o)));
        return static_cast<vm_State *>(to_external(o))->m_val;
    }

    static vm_obj to_obj(State const & s) {
        return mk_vm_external(new(get_vm_allocator().allocate(sizeof(vm_State))) vm_State(s));
    }

    static bool is_silent_exception(vm_obj const & ex) {
        return is_constructor(ex) && cidx(ex) == 1 && is_none(cfield(ex, 0));
    }

    static vm_obj mk_result(vm_obj const & a, vm_obj const & s) {
        lean_assert(is_state(s));
        return mk_vm_constructor(0, a, s);
    }

    static bool is_result_exception(vm_obj const & r) {
        return is_constructor(r) && cidx(r) == 1;
    }

    static bool is_result_success(vm_obj const & r) {
        return is_constructor(r) && cidx(r) == 0;
    }

    static vm_obj get_result_value(vm_obj const & r) {
        lean_assert(is_result_success(r));
        return cfield(r, 0);
    }

    static vm_obj get_result_state(vm_obj const & r) {
        lean_assert(is_result_success(r));
        return cfield(r, 1);
    }

    static vm_obj mk_success(vm_obj const & a, State const & s) {
        return mk_vm_constructor(0, a, to_obj(s));
    }

    static vm_obj mk_success(State const & s) {
        return mk_success(mk_vm_unit(), s);
    }

    static vm_obj mk_exception(vm_obj const & fn, State const & s) {
        return mk_vm_constructor(1, mk_vm_some(fn), mk_vm_none(), to_obj(s));
    }

    static vm_obj mk_silent_exception(State const & s) {
        return mk_vm_constructor(1, mk_vm_none(), mk_vm_none(), to_obj(s));
    }

    static vm_obj mk_exception(vm_obj const & fn, vm_obj const & pos, State const & s) {
        return mk_vm_constructor(1, mk_vm_some(fn), pos, to_obj(s));
    }

    static vm_obj mk_exception(throwable const & ex, State const & s) {
        vm_obj _ex = lean::to_obj(ex);
        vm_obj fn = mk_vm_closure(get_throwable_to_format_fun_idx(), 1, &_ex);
        optional<pos_info> pos;
        if (auto kex = dynamic_cast<exception_with_pos const *>(&ex))
            pos = kex->get_pos();
        vm_obj _pos = pos ? mk_vm_some(mk_vm_pair(mk_vm_nat(pos->first), mk_vm_nat(pos->second))) : mk_vm_none();
        return mk_exception(fn, _pos, s);
    }

    static vm_obj mk_exception(format const & fmt, State const & s) {
        vm_state const & S = get_vm_state();
        if (optional<vm_decl> K = S.get_decl(get_combinator_K_name())) {
            return mk_exception(mk_vm_closure(K->get_idx(), lean::to_obj(fmt), mk_vm_unit(), mk_vm_unit()), s);
        } else {
            throw exception("failed to create tactic exceptional result, combinator.K is not in the environment, "
                                    "this can happen when users are hacking the init folder");
        }
    }

    static vm_obj mk_exception(char const * msg, State const & s) {
        return mk_exception(format(msg), s);
    }

    static vm_obj mk_exception(sstream const & strm, State const & s) {
        return mk_exception(strm.str().c_str(), s);
    }

    static vm_obj mk_exception(std::function<format()> const & thunk, State const & s) {
        return mk_exception(mk_vm_format_thunk(thunk), s);
    }

    static void report_exception(vm_state & S, vm_obj const & r) {
        if (optional<exception_info> ex = is_exception(S, r)) {
            format fmt = std::get<0>(*ex);
            optional<pos_info> pos = std::get<1>(*ex);
            throw formatted_exception(pos, fmt);
        }
    }

    /* If r is (interaction_monad.result.success a s), then return s */
    static optional<State> is_success(vm_obj const & r) {
        if (is_result_success(r))
            return some(to_state(cfield(r, 1)));
        return {};
    }

    typedef std::tuple<format, optional<pos_info>, State> exception_info;

    /* If ex is (interaction_monad.result.exception (some fn) _ _), then return (fn ()).
       The vm_state S is used to execute (fn ()). */
    static optional<exception_info> is_exception(vm_state & S, vm_obj const & ex) {
        if (is_result_exception(ex) && !is_none(cfield(ex, 0))) {
            vm_obj fmt = S.invoke(get_some_value(cfield(ex, 0)), mk_vm_unit());
            optional<pos_info> p;
            if (!is_none(cfield(ex, 1))) {
                auto vm_p = get_some_value(cfield(ex, 1));
                p = some(mk_pair(to_unsigned(cfield(vm_p, 0)), to_unsigned(cfield(vm_p, 1))));
            }
            return optional<exception_info>(to_format(fmt), p, to_state(cfield(ex, 2)));
        } else {
            return {};
        }
    }

    class evaluator {
        type_context & m_ctx;
        options const & m_opts;

    protected:
        virtual void process_failure(vm_state & S, vm_obj const & r) {
            report_exception(S, r);
            /* Do nothing if it is a silent failure */
            lean_assert(is_silent_exception(r));
        }

    public:
        environment compile(name const & interaction_name, expr const & interaction) {
            pos_info_provider * provider = get_pos_info_provider();
            expr interaction_type = m_ctx.infer(interaction);
            environment new_env = m_ctx.env();
            bool use_conv_opt = true;
            bool is_trusted = false;
            auto cd = check(new_env,
                            mk_definition(new_env, interaction_name, {}, interaction_type, interaction, use_conv_opt,
                                          is_trusted));
            new_env = new_env.add(cd);
            if (auto pos = provider->get_pos_info(interaction))
                new_env = add_transient_decl_pos_info(new_env, interaction_name, *pos);
            try {
                bool optimize_bytecode = false;
                return vm_compile(new_env, new_env.get(interaction_name), optimize_bytecode);
            } catch (exception & ex) {
                throw formatted_exception(some(interaction), format(ex.what()));
            }
        }

        vm_obj invoke(vm_state & S, name const & interaction_name, std::initializer_list<vm_obj> const & args) {
            vm_state::profiler prof(S, m_opts);
            vm_obj r = S.invoke(interaction_name, args);
            if (prof.enabled()) {
                prof.get_snapshots().display("tactic", m_opts, get_global_ios().get_regular_stream());
            }
            return r;
        }

        evaluator(type_context & ctx, options const & opts) : m_ctx(ctx), m_opts(opts) {}

        virtual vm_obj operator()(expr const & interaction, State const & s) {
            name interaction_name("_interaction");
            environment new_env = compile(interaction_name, interaction);
            vm_state S(new_env, m_opts);
            vm_state::profiler prof(S, m_opts);
            vm_obj r = S.invoke(interaction_name, {to_obj(s)});
            if (prof.enabled()) {
                auto out = message_builder(environment(), get_global_ios(),
                                           get_pos_info_provider()->get_file_name(),
                                           get_pos_info_provider()->get_pos_info_or_some(interaction),
                                           INFORMATION);
                out.set_caption("tactic profile data");
                if (prof.get_snapshots().display("tactic", m_opts, out.get_text_stream().get_stream()))
                    out.report();
            }

            if (!is_success(r))
                process_failure(S, r);
            return r;
        }
    };
};

}
