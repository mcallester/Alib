
/** ========================================================================
Algbra requires functions
========================================================================**/

declare_package(`algebra);
/***  {41;done}***/

clear_event(start_algebra); 
/***  after 22 id_is_a_perm;***/

define start_algebra true; 
/***  event 23 max_exps 0 net_exps 0 rules 0***/

/** ========================================================================
group definition
========================================================================**/
break_on_user_error[0]=1;
/***  {42;done}***/

define magma(s:type){class(){op:s=>s=>s}};
/***  event 24 max_exps 62 net_exps 57 rules 386***/

define semigroup(s:type){class (magma(s)){is(op,associative)}};
/***  event 25 max_exps 909 net_exps 909 rules 1866***/

define group(s:type){class (semigroup(s)){
  id:s;
  forall(x:s){op(id,x) = x && op(x,id) = x};
  inv:s=>s;
  forall(x:s){op(inv(x),x) = id && op(x,inv(x)) = id}}};
/***  event 26 max_exps 3052 net_exps 1775 rules 19083***/

define test (s:type;G:group(s)){is(G,group)};
/***  event 27 max_exps 291 net_exps 211 rules 3276***/

sugar_noname(intern_exp(`test))
/***  {
    43;
    lambda(s:type,X:group(s)){is(X,group(s))}}***/
