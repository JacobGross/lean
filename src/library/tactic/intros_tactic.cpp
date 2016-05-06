/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "util/fresh_name.h"
#include "kernel/instantiate.h"
#include "library/constants.h"
#include "library/reducible.h"
#include "library/tactic/intros_tactic.h"
#include "library/tactic/expr_to_tactic.h"

namespace lean {
static tactic intro_intros_tactic(list<name> _ns, bool is_intros) {
    auto fn = [=](environment const & env, io_state const &, proof_state const & s) {
        list<name> ns    = _ns;
        goals const & gs = s.get_goals();
        if (empty(gs)) {
            throw_no_goal_if_enabled(s);
            return optional<proof_state>();
        }
        goal const & g      = head(gs);
        auto tc             = mk_type_checker(env);
        expr t              = g.get_type();
        expr m              = g.get_meta();
        bool gen_names      = is_intros && empty(ns);
        bool gen_one_name   = !is_intros && empty(ns);
        bool first          = true;
        try {
            while (true) {
                if (!gen_names && (!gen_one_name || !first) && is_nil(ns))
                    break;
                if (!is_pi(t)) {
                    if (!is_nil(ns)) {
                        t = tc->ensure_pi(t).first;
                    } else {
                        expr new_t = tc->whnf(t).first;
                        if (!is_pi(new_t))
                            break;
                        t = new_t;
                    }
                }
                name new_name;
                if (!is_nil(ns)) {
                    new_name = head(ns);
                    if (new_name == "_")
                        new_name = get_unused_name(binding_name(t), m);
                    ns       = tail(ns);
                } else {
                    new_name = get_unused_name(binding_name(t), m);
                }
                expr new_local = mk_local(mk_fresh_name(), new_name, binding_domain(t), binding_info(t));
                t              = instantiate(binding_body(t), new_local);
                m              = mk_app(m, new_local);
                first          = false;
            }
            goal new_g(m, t);
            return some(proof_state(s, goals(new_g, tail(gs))));
        } catch (exception &) {
            return optional<proof_state>();
        }
    };
    return tactic01(fn);
}

tactic intro_tactic(list<name> const & ns) {
    return intro_intros_tactic(ns, false);
}

tactic intros_tactic(list<name> const & ns) {
    return intro_intros_tactic(ns, true);
}

void initialize_intros_tactic() {
    register_tac(get_tactic_intro_name(),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<name> ns;
                     get_tactic_id_list_elements(app_arg(e), ns, "invalid 'intro' tactic, arguments must be identifiers");
                     return intro_tactic(to_list(ns.begin(), ns.end()));
                 });
    register_tac(get_tactic_intros_name(),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<name> ns;
                     get_tactic_id_list_elements(app_arg(e), ns, "invalid 'intros' tactic, arguments must be identifiers");
                     return intros_tactic(to_list(ns.begin(), ns.end()));
                 });
}

void finalize_intros_tactic() {
}
}
