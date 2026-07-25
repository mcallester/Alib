
/** ========================================================================
Algbra requires functions
========================================================================**/

load_mode[0] = 1; 
/** {38;done} **/

declare_package(`algebra);
/** {39;done} **/

clear_event(start_algebra); 
/** the event start_algebra is not present **/

define start_algebra true; 
/** event 17 max 0 net 0 **/

/** ========================================================================
group definition
========================================================================**/

define magma(s:type){class(){op:s=>s=>s}};
/** event 18 max 35 net 35 **/

define semigroup(s:type){class (magma(s)){is(op,associative)}};
/** event 19 max 231 net 228 **/

define group(s:type){class (semigroup(s)){
  id:s;
  forall(x:s){op(id,x) = x && op(x,id) = x};
  inv:s=>s;
  forall(x:s){op(inv(x),x) = id && op(x,inv(x)) = id}}};
/** event 20 max 637 net 626 **/

