
restart_event(`schroeder_bernstein_functions);
/** {30;done} **/

declare_package(`schroeder_bernstein_functions);
/** {31;done} **/

theorem emptyset_exists(){
  exists(s:set){not(inhabited(s))}}{
  let(s:set,empty=assert(x:s){not(x=x)}){}};
/** {32;done} **/

define injection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      unique(assert(x:s){y = f(x)})}
    }};
/** {33;done} **/

define surjection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      exists(x:s){f(x)=y}}}};
/** {34;done} **/

define bijection(s:set,w:set){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};
/** {35;done} **/

theorem bijections_invert (s:set, w:set) {implies(inhabited(bijection(s,w)), inhabited(bijection(w,s)))} {
  let(f:bijection(s,w)){
    let(g = lambda(x:w){the(y:s){f(y)=x}})}};
/** {36;done} **/

theorem empty_uniqueness (c:class) {
  unique(assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))})};
/** {37;done} **/

break_on_throw_event[0]=0;
/** {38;done} **/

theorem Schroeder_Bernstein (s:set, w:set) {
  implies(inhabited(injection(s,w))&&inhabited(injection(w,s)),
          inhabited(bijection(s,w)))}{
  suppose(inhabited(injection(s,w))&&inhabited(injection(w,s))){
    let(f:injection(s,w),
        g:injection(w,s),
        use_f =μ lambda(x:s){
          not(exists(y:w){
                g(y)=x
                && not(exists(z:s){
                         f(z)=y && use_f(z)})})}){
      let(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
        show(is(h,surjection(s,w))){
          lemma{
            let(x1:w){
              show(exists(x2:s){h(x2)=x1}){
                /* let(z:assert(z:s){f(z)=x1 && use_f(z)}) */
                suppose(use_f(g(x1))){
                  consider(g(x1),assert(x2:s){f(x2)=x1})}
                /* { */
                  /*   suppose(use_f(g(x1))){ */
                    /*     show(exists(z:s){f(z)=x1 && use_f(z)})} */
                  /*   } */
              }
              }}}}}}};
/** {
    in context;
    s:set;
    w:set;
    show implies(and(inhabited(injection(s,w)),
                     inhabited(injection(w,s))),
                 inhabited(bijection(s,w)))for user_show;
    assume and(inhabited(injection(s,w)),
               inhabited(injection(w,s)));
    f:injection(s,w);
    g:injection(w,s);
    let use_f=mu(fun_1:arrow(s,bool)){
      lambda(x_1:s){
        not(exists(x_2:w){
              and(equal(g(x_2),x_1),
                  not(exists(x_3:s){
                        and(equal(f(x_3),x_2),
                            fun_1(x_3))}))})}};
    let h=lambda(x_1:s){
      if(use_f(x_1),
         f(x_1),
         the(x_2:w){equal(g(x_2),x_1)})};
    --------backchaining---------- ;
    focus on s from goal_free_variable;
    focus on w from goal_free_variable;
    local_cases;
    assume not(implies(and(inhabited(injection(s,w)),
                           inhabited(injection(w,s))),
                       inhabited(bijection(s,w))));
    assume and(inhabited(assert(fun_1:arrow(s,w)){
                           forall(x_1:w){
                             unique(assert(x_2:s){equal(x_1,fun_1(x_2))})}}),
               inhabited(assert(fun_1:arrow(w,s)){
                           forall(x_1:s){
                             unique(assert(x_2:w){equal(x_1,fun_1(x_2))})}}));
    local_cases;
    assume not(inhabited(assert(fun_1:arrow(s,w)){
                           and(forall(x_1:w){
                                 unique(assert(x_2:s){equal(x_1,fun_1(x_2))})},
                               forall(x_1:w){
                                 exists(x_2:s){equal(fun_1(x_2),x_1)}})}));
    local_cases;
    assume not(exists(fun_1:arrow(s,w)){
                 and(forall(x_1:w){
                       unique(assert(x_2:s){equal(x_1,fun_1(x_2))})},
                     forall(x_1:w){
                       exists(x_2:s){equal(fun_1(x_2),x_1)}})});
    Failure to show goal or subgoal;
    exists(fun_1:arrow(s,w)){
      and(forall(x_1:w){
            unique(assert(x_2:s){equal(x_1,fun_1(x_2))})},
          forall(x_1:w){
            exists(x_2:s){equal(fun_1(x_2),x_1)}})}} **/

define inverse(s:set,w:set,f:bijection(s,w)){
  assert(g:bijection(w,s)){
    forall(x:w){f(g(x))=x} &&
    forall(y:s){g(f(y))=y}}};
/** {39;done} **/

theorem inverses_exist (s:set, w:set, f:bijection(s,w)){
  inhabited(inverse(s,w,f))}{
  let(g = lambda(x:w){the(y:s){f(y)=x}}){
    lemma{show(is(g,bijection(w,s)))}}
  };
/** {40;done} **/
