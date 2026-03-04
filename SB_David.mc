
restart_event(`schroeder_bernstein_functions);
/** {33;done} **/

declare_package(`schroeder_bernstein_functions);
/** {34;done} **/

/** ========================================================================
empty set exists
========================================================================**/

break_on_throw_context[0] = 1;
/** {35;done} **/

check_for_corruption[0] = 1;
/** {36;done} **/

check_depth[0] = 8;
/** {37;done} **/

clear_current_event();
/** {
    in context;
    attempt to clear non-existent current event} **/

theorem emptyset_exists{
  exists(s:set){empty(s)}
  }{
  show (s:set){empty(assert(x:s){not(x=x)})}
  };
/** {
    in context;
    1.___ intern_cps_quantifier_ exists ___;
    2.intern_cps_decl(s:set);
    to continue context_pop run step();} **/

step();
/** {
    in context;
    1.push_goal(exists(bound_s:set){empty(bound_s)});
    2.show_decl(s:set);
    3.___ intern_cps_quantifier_ assert ___;
    4.intern_cps_decl(x:s);
    to continue context_pop run step();} **/

define preimage(s:set, w:set, y:w, h:s=>w){
  assert(x:s){h(x)=y}};

define injection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      unique(preimage(s,w,y,f))}}};

define surjection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      inhabited(preimage(s,w,y,f))}}};

define bijection(s:set,w:set){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};

//three versions of bijections_invert. Identical except for the
//injection proof which is modified to exhibit the issue motivating
//congruence on quantified expressions, with the last one requiring the bvars.

theorem bijections_invert(s:set, w:set){
  implies(inhabited(bijection(s,w)), inhabited(bijection(w,s)))
  }{
  with(f:bijection(s,w),
       g = lambda(x:w){the(y:s){f(y)=x}}){
    show(){is(g,injection(w,s))}{
      show(y:s, x1:assert(x:w){g(x)=y}, x2:assert(x:w){g(x)=y}){x1=x2}{
        show(){f(y)=x1}{with(focus(x1))};
        show(){f(y)=x2}{with(focus(x2));};};
      with(focus(g))};
    show(){is(g,surjection(w,s))}{
      show(x:s){is(f(x), preimage(w,s,x,g))};};
    show(){is(g,bijection(w,s))}; 
    }};

theorem bijections_invert(s:set, w:set){
  implies(inhabited(bijection(s,w)), inhabited(bijection(w,s)))
  }{
  with(f:bijection(s,w),
       g = lambda(x:w){the(y:s){f(y)=x}})
  { show(){is(g,injection(w,s))}{
      with(y:s){
        show(x1:preimage(w,s,y,g), x2:preimage(w,s,y,g)) {x1=x2};}};
    show(){is(g,surjection(w,s))}{
      show(x:s){is(f(x), preimage(w,s,x,g))};};
    show(){is(g,bijection(w,s))}; 
    }};

// this one requires congruence on quantified expressions in the injective case
theorem bijections_invert(s:set, w:set){
  implies(inhabited(bijection(s,w)), inhabited(bijection(w,s)))
  }{
  with(f:bijection(s,w),
       g = lambda(x:w){the(y:s){f(y)=x}})
  { show(){is(g,injection(w,s))}{
      with(y:s){
        show(x1:assert(x:w){g(x)=y}, x2:assert(x:w){g(x)=y}) {x1=x2};}};
    show(){is(g,surjection(w,s))}{
      show(x:s){is(f(x), preimage(w,s,x,g))};};
    show(){is(g,bijection(w,s))}; 
    }};


theorem empty_uniqueness (c:class) {
  unique(assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))})}{
  with(){
    show(x1:assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))},
         x2:assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))}){
      x1=x2
      }{
      show(){x1 = lambda(z:c){x1(z)}};
      show(){x2 = lambda(z:c){x2(z)}};
      show(y:c){x1(y)=x2(y)}{
        show{implies(x1(y),x2(y))};
        show{implies(x2(y),x1(y))};};};}};

theorem test_injectivity (s:set, w:set, f:injection(s,w), x_2:s, x_3:s, f(x_2)=f(x_3)){
  x_2=x_3}{
  with(focus(f(x_2)), focus(x_3), focus(x_2))};

theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  with(f:injection(s,w),
       g:injection(w,s),
       use_f =μ lambda(x:s){
         not(exists(y:preimage(w,s,x,g)){
               not(exists(z:preimage(s,w,y,f)){
                     use_f(z)})})}){
    
    show(x:s){
      use_f(x) = use_f(g(f(x)))}{
      with(assert_type_from_use_f = 
           assert(yyy:preimage(w,s,g(f(x)),g)){
             not(exists(xxx:preimage(s,w,yyy,f)){
                   use_f(xxx)})}){
        
        //it would be helpful for user to indicate intention about habitation and system to complain
        //here we need refutation to see type habitation and that isn't tried in adjust_formula because we don't have a way to tell it our expectation
        show_case(not(inhabited(assert_type_from_use_f))){
          with(assume_not_goal, focus(x), focus(f(x)), focus(g(f(x))))
          };
        
        //it would be helpful for user to indicate intention about habitation and system to complain
        with(assume_not_goal, //needed here to see next type inhabited. NOTE: no way to specify this analysis on the way out/popping
             yy:assert_type_from_use_f){
          show{yy=f(x)}{with(focus(yy), focus(x), focus(f(x)), focus(g(f(x))),)}; //any such yy is f(x) given injectivity of g
          }}};
    
    with(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
      show(){is(h,injection(s,w))}{
        show(y:w,
             x_2:preimage(s,w,y,h),
             x_3:preimage(s,w,y,h)){
          x_2 = x_3
          }{
          show(use_f(x_2)){use_f(x_3)}{with(focus(x_2), assume_not_goal)};
          show(use_f(x_3)){use_f(x_2)}{with(focus(x_3), assume_not_goal)};
          with(assume_not_goal,focus(x_2), focus(x_3))}};

      show(){is(h,surjection(s,w))}{
        show(y:w){exists(x:s){h(x)=y}}{
          show_case(not(inhabited(preimage(s,w,y,f)))){
            with(focus(y), focus(g(y))){
              show{not(use_f(g(y)))}{
                with(assume_not_goal)};}};
          show_case(use_f(g(y))){
            //this case unfinished
            with(pre = the(preimage(s,w,y,f))){
              show{is(y,preimage(w,s,g(y),g))};
              show(use_f(pre)){
                with(focus(g(y)),focus(y), focus(pre), assume_not_goal)};
              with(focus(g(y)),
                   focus(pre))}}}}}}};


//WORKING PROOF OF INJECTION SUPERSEDED ABOVE
// injection works but needs exploration. Also still want to try the() and taxonomic
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  with(f:injection(s,w),
       g:injection(w,s),
       use_f =μ lambda(x:s){
         not(exists(y:preimage(w,s,x,g)){
               not(exists(z:preimage(s,w,y,f)){
                     use_f(z)})})}){
    with(h = lambda(x:s){if(use_f(x),f(x),the(y:w){g(y)=x})}){
      show(){is(h,injection(s,w))}{
        show(x:s){use_f(x) |=> f(x)=h(x)};
        show(x:s){not(use_f(x)) |=> the(y:w){g(y)=x}=h(x)};
        show(y:w){unique(preimage(s,w,y,f))};
        show(x:s){unique(preimage(w,s,x,g))};
        
        //show(x:s){is(preimage(w,s,x,g),w)}; need guidance on this
        
        show(x:s, //apply fixed point of use_f
             not(use_f(x)),
             y:preimage(w,s,x,g),
             xx:preimage(s,w,y,f)){
          not(use_f(xx))}{
          with(yy:assert(yyy:preimage(w,s,x,g)){
                 not(exists(xxx:preimage(s,w,yyy,f)){use_f(xxx)})}){
            show{yy=y}{with(focus(y), focus(yy))};}};
        
        //explore why this doesn't eliminate the body in show_case_contradictory
        //show(x:s,
               //   not(use_f(x))){
          //forall(y:preimage(w,s,x,g)){
            //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
        show(x_1:w,
             x_2:preimage(s,w,x_1,h),
             x_3:preimage(s,w,x_1,h)){
          x_2 = x_3
          }{
          show_case_contradictory(use_f(x_2) && not(use_f(x_3))){
            with(focus(x_3), focus(x_1), focus(x_2)){
              //show{forall(y:preimage(w,s,x_3,g)){
                  //  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              show{forall(y:preimage(w,s,x_3,g)){
                  not(exists(z:preimage(s,w,y,f)){use_f(z)})}};
              }};
          show_case_contradictory(use_f(x_3) && not(use_f(x_2))){
            with(focus(x_3), focus(x_1), focus(x_2))};
          with(assume_not_goal,focus(x_2), focus(x_3)){
            show_case(use_f(x_3))}}};
      show(){is(h,surjection(s,w))}{
        show(x1:w){exists(x2:s){h(x2)=x1}}{
          show_case(use_f(g(x1))){
            with(focus(g(x1)),
                 z:assert(x2:s){f(x2)=x1},
                 focus(z))}}}}}};


//trying ontic approach
theorem Schroeder_Bernstein (s:set, w:set, inhabited(injection(s,w))&&inhabited(injection(w,s))) {
  inhabited(bijection(s,w))}{
  
  with(f:injection(s,w),
       g:injection(w,s),
       covered_by_g =μ lambda(y:w){
         not(inhabited(preimage(s,w,y,f))) 
         || exists(yy:w){covered_by_g(yy) && y=f(g(yy))}}){
    show(x:s,covered_by_g(f(x))){ //the() safety for defining h()
      inhabited(preimage(w,s,x,g))}{
      with(focus(f(x)), //needed to avoid existence supposition for y:
           y:assert(yy:w){covered_by_g(yy) && f(x)=f(g(yy))}){
        show{is(y,preimage(w,s,x,g))}{
          show{x=g(y)}{with(focus(g(y)))};};}};
    with(uses_g = lambda(x:s){exists(y:preimage(w,s,x,g)){covered_by_g(y)}},
         h = lambda(x:s){if(uses_g(x),
                            the(preimage(w,s,x,g)),
                            f(x))}){
      show(){is(h,injection(s,w))}{
        show(y:w,
             x_2:preimage(s,w,y,h),
             x_3:preimage(s,w,y,h)){
          x_2=x_3}{
          show_case(uses_g(x_2)){
            show{unique(preimage(w,s,x_2,g))}{with(focus(x_2))};
            show{h(x_2)=the(preimage(w,s,x_2,g))};
            show{h(x_2)=y};
            show{covered_by_g(y)};
            show_case(not(uses_g(x_3))){
              
              };
            with(focus(x_2),focus(x_3))
            };
          show_case(not(uses_g(x_2)));}};}}};

//not used below here, obsolete
define inverse(s:set,w:set,f:bijection(s,w)){
  assert(g:bijection(w,s)){
    forall(x:w){f(g(x))=x} &&
    forall(y:s){g(f(y))=y}}};

theorem inverses_exist (s:set, w:set, f:bijection(s,w)){
  inhabited(inverse(s,w,f))}{
  let(g = lambda(x:w){the(y:s){f(y)=x}}){
    lemma{show(is(g,bijection(w,s)))}}
  };
