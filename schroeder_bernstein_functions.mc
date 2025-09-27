
restart_event(`schroeder_bernstein_functions);

declare_package(`schroeder_bernstein_functions);

break_on_throw[0]=1;

theorem emptyset_exists(){
  exists(s:set){not(inhabited(s))}}{
  let(s:set,
      empty=assert(x:s){not(x=x)}){
    suppose_not{let(x:empty)}}};

define injection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      unique(assert(x:s){y = f(x)})}
    }};

define surjection(s:set,w:set){
  assert(f:s=>w){
    forall(y:w){
      exists(x:s){f(x)=y}}}};

define bijection(s:set,w:set){
  assert(f:s=>w){
    is(f,injection(s,w)) && is(f,surjection(s,w))}};

theorem bijections_invert (s:set, w:set) {implies(inhabited(bijection(s,w)), inhabited(bijection(w,s)))} {
  let(f:bijection(s,w)){
    let(g = lambda(x:w){the(y:s){f(y)=x}})}};

theorem empty_uniqueness (c:class) {
  unique(assert(phi:c=>bool){not(inhabited(assert(s:c){phi(s)}))})};

theorem test_injectivity (s:set, w:set, f:injection(s,w), x_2:s, x_3:s){
  implies(f(x_2)=f(x_3), x_2=x_3)}{
  show(unique(assert(xx:s){f(x_2) = f(xx)})){consider(f(x_2))}
  };

define preimage(s:set, w:set, y:w, h:s=>w){
  assert(x:s){h(x)=y}};

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
        show(is(h,injection(s,w))){
          lemma{let(x:s){show(use_f(x) |=> f(x)=h(x))}};
          lemma{let(x:s){show(not(use_f(x)) |=> the(y:w){g(y)=x}=h(x))}};
          lemma{let(y:w){show(unique(preimage(s,w,y,f)))}};
          lemma{
            let(x_1:w,
                x_2:preimage(s,w,x_1,h),
                x_3:preimage(s,w,x_1,h)){
              show(x_2 = x_3){
                suppose_for_refutation(use_f(x_2) && not(use_f(x_3))){
                  show(exists(y:w){g(y)=x_3 && not(exists(z:s){f(z)=x_1 && use_f(z)})});
                  let(xx:assert(y:w){
                        g(y)=x_3 && not(exists(z:s){f(z)=x_1 && use_f(z)})})};
                suppose_for_refutation(use_f(x_3) && not(use_f(x_2))){
                  show(exists(y:w){g(y)=x_2 && not(exists(z:s){f(z)=x_1 && use_f(z)})});
                  let(xx:assert(y:w){g(y)=x_2 && not(exists(z:s){f(z)=x_1 && use_f(z)})})};
                suppose_not{suppose(use_f(x_3))}}}}};
        show(is(h,surjection(s,w))){
          lemma{
            let(x1:w){
              show(exists(x2:s){h(x2)=x1}){
                suppose(use_f(g(x1))){
                  consider(g(x1),assert(x2:s){f(x2)=x1})}}}}
          }}}}};



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
