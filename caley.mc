
/** ========================================================================
requires functions and algebra
========================================================================**/

load_mode[0] = 1; /** {38;done} **/
/** {41;done} **/

declare_package(`caley); /** {39;done} **/
/** {40;done} **/

clear_event(start_caley); /** the event start_caley is not present **/
/** after 22 test; **/

define start_caley true; /** event 22 max 0 net 0 **/
/** event 23 max 0 net 0 **/

/** ========================================================================
The caley group
========================================================================**/

define caley_group(s:type,G:group(s)){
  obj(group(permutation(s))){
    op = composition;
    id = identity;
    inv = bij_inverse}
  };
/** {
    in 24 caley_group;
    1.intern_decl(s:type);
    2.intern_decl(G:group(s));
    3.invariant violation: !mze||safep(mze);
    4.BREAKPOINT;} **/

sugar(clean(type_of(intern_exp(`composition))))
/** {
  43;
  pi(bound_s:type,
     bound_s_2:type,
     bound_s_3:type){
    arrow(arrow(bound_s_2,bound_s_3),
	  arrow(arrow(bound_s,bound_s_2),
		arrow(bound_s,bound_s_3)))}} **/

//is(composition,  arrow(
//		       arrow(s,s),
//		       arrow(arrow(s,s)),
//			     arrow(arrow(s,s)))))

