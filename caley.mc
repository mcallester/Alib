
/** ========================================================================
requires functions and algebra
========================================================================**/

load_mode[0] = 1; /** {38;done} **/
/** {38;done} **/

declare_package(`caley); /** {39;done} **/
/** {39;done} **/

clear_event(start_caley); /** the event start_caley is not present **/
/** the event start_caley is not present **/

where();
/** {after 21 group;} **/

define start_caley true; /** event 22 max 0 net 0 **/
/** event 22 max 0 net 0 **/

/** ========================================================================
The caley group
========================================================================**/

define caley_group(G:group){
  obj(group){
    member = permutation(G.member);
    op = lambda(f:permutation(G.member),g:permutation(G.member)){composition(f,g)};
    id = id_fun(G.member);
    inv = bij_inverse(G.member,G.member)}};
/** event 23 max 5539 net 3683 **/
