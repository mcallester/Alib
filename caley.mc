
/**
========================================================================
requires functions and algebra
========================================================================**/

load_mode[0] = 1; /** {38;done} **/
/** {38;done} **/

declare_package(`caley); /** {39;done} **/
/** {39;done} **/

clear_event(start_caley); /** the event start_caley is not present **/
/** after 21 group; **/

where();
/** {after 21 group;} **/

define start_caley true; /** event 22 max 0 net 0 **/
/** event 22 max 0 net 0 **/

/** ========================================================================
The caley group
========================================================================**/

desugar(`{lambda(w:type,x:w){obj(group){member=w;id=x}}})
/** {
    40;
    lambda(w,
           type,
           lambda(x,
                  w,
                  obj(group,
                      valcons(tag(quote(member),w),
                              tag(quote(id),x)))))} **/

where();
/** {after 22 start_caley;} **/

define caley_group(G:group){
  obj(group){
    member = permutation(G.member);
    op = lambda(f:permutation(G.member),g:permutation(G.member)){composition(f,g)};
    id = id_fun(G.member);
    inv = bij_inverse(G.member)}};
/** {non-break error (likely a segment fault) --- to resume type p NIDE()} **/

/**   **/




where();
/** {after 21 group;} **/
