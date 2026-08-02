
/** ========================================================================
requires functions and algebra
========================================================================**/

load_mode[0] = 1; /** {38;done} **/
/** {42;done} **/

declare_package(`caley); /** {39;done} **/
/** {43;done} **/

clear_event(start_caley); /** the event start_caley is not present **/
/** after 23 test; **/

define start_caley true; /** event 22 max 0 net 0 **/
/** event 24 max 0 net 0 **/

/** ========================================================================
The caley group
========================================================================**/

define caley_group(s:type,G:group(s)){
  obj(group(permutation(s))){
    op = composition;
    id = identity;
    inv = bij_inverse}
  };
/** event 25 max 1834 net 1611 **/

