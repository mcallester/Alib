
/** ========================================================================
Algbra requires functions
========================================================================**/

declare_package(`algebra);
/***  {37;done}***/

clear_event(start_algebra); 
/***  the event start_algebra is not present***/

define start_algebra true; 
/***  event 27 max_exps 0 net_exps 0 rules 0***/

/** ========================================================================
group definition
========================================================================**/
break_on_user_error[0]=1;
/***  {38;done}***/

define magma(s:type){class(){op:s=>s=>s}};
/***  event 28 max_exps 31 net_exps 31 rules 26***/

define semigroup(s:type){class (magma(s)){is(op,associative)}};
/***  event 29 max_exps 4104 net_exps 369 rules 2835***/

define group(s:type){class (semigroup(s)){
  id:s;
  forall(x:s){op(id,x) = x && op(x,id) = x};
  inv:s=>s;
  forall(x:s){op(inv(x),x) = id && op(x,inv(x)) = id}}};
/***  event 30 max_exps 5267 net_exps 439 rules 8963***/

define test (s:type,G:group(s)){is(G,group)};
/***  event 31 max_exps 124 net_exps 91 rules 165***/

sugar_noname(intern_exp(`test))
/***  {
    39;
    lambda(bound_s:type,
           bound_Obj:class{
             op:arrow(bound_s,
                      arrow(bound_s,bound_s));
             is(op,associative(bound_s));
             id:bound_s;
             forall(bound_x:bound_s){
               and(equal(op(id,bound_x),bound_x),
                   equal(op(bound_x,id),bound_x))};
             inv:arrow(bound_s,bound_s);
             forall(bound_x:bound_s){
               and(equal(op(inv(bound_x),bound_x),
                         id),
                   equal(op(bound_x,inv(bound_x)),
                         id))}}){
      is(bound_Obj,group(bound_s))}}***/
