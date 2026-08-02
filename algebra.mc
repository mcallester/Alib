
/** ========================================================================
Algbra requires functions
========================================================================**/

load_mode[0] = 1; 
/** {39;done} **/

declare_package(`algebra);
/** {40;done} **/

clear_event(start_algebra); 
/** the event start_algebra is not present **/

define start_algebra true; 
/** event 19 max 0 net 0 **/

/** ========================================================================
group definition
========================================================================**/

define magma(s:type){class(){op:s=>s=>s}};
/** event 20 max 35 net 35 **/

define semigroup(s:type){class (magma(s)){is(op,associative)}};
/** event 21 max 231 net 228 **/

define group(s:type){class (semigroup(s)){
  id:s;
  forall(x:s){op(id,x) = x && op(x,id) = x};
  inv:s=>s;
  forall(x:s){op(inv(x),x) = id && op(x,inv(x)) = id}}};
/** event 22 max 637 net 626 **/

define test (s:type,G:group(s)){is(G,group)};
/** event 23 max 125 net 94 **/

sugar_noname(intern_exp(`test))
/** {
    41;
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
      is(bound_Obj,group(bound_s))}} **/
