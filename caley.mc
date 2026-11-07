
/** ========================================================================
requires functions and algebra
========================================================================**/

declare_package(`caley);
/***  {40;done}***/

clear_event(start_caley); /** the event start_caley is not present **/
/***  after 31 test;***/

define start_caley true; /** event 22 max 0 net 0 **/
/***  event 32 max_exps 0 net_exps 0 closures 0***/

/** ========================================================================
The caley group
========================================================================**/

define caley_group(s:type,G:group(s)){
  obj(group(permutation(s))){
    op = perm_composition;
    id = identity;
    inv = bij_inverse}
  };
/***  ***/

Group:type->type

G:group(s)

f:G.member -> permutation(G.member)

Carry(Group,f)(G.op) = Caley(G).op


