// Cloudflare managed-challenge main.js (build aae2b9a1c261), de-obfuscated. The obfuscator replaces every operator with a map lookup {"<key>": fn(a,b){return a OP b}}; the string keys (gypWF, cyxhk, …) are stable across the file. See deobfuscation.md § Rosetta stone for the full key->operator / type-code / _cf_chl_opt tables.
window._cf_chl_opt= {
  STupN6:'g'}
;
~// decoder -> fa
function(decoder,
// globalRef -> b
globalRef,
// doc -> e
doc,
// DEFLATE compressor (LZ77 hash + Huffman, classic length/distance tables)
// deflateCompress -> p
deflateCompress,
// encoding module: builds { utf8Encode, base64Encode, xorCrypt, fnv1aHash, hashMix, encodePayload }
// encoderModule -> A
encoderModule,
// typeCodes -> U
typeCodes,
// typeCode -> G
typeCode,
// messageTypes -> T
messageTypes,
// isMessageType -> V
isMessageType,
// pollIntervalMs -> a
pollIntervalMs,
// pollTimer -> E
pollTimer,
// intervalState -> I
intervalState,
// hasState -> z
hasState,
// challengeOpts -> x
challengeOpts,
// submit the solve to /jsd/oneshot via XHR POST
// submitOneshot -> n
submitOneshot,
M) {
  decoder=decodeString,
  function(l,
  c,
  gw,
  fv,
  d,
  P) {
    for(gw= {
      l:245,
      c:284,
      d:452,
      P:333,
      R:222,
      H:399,
      Z:394,
      C:460,
      O:315,
      X:435,
      f0:344,
      f1:297,
      f2:418}
,
    fv=decodeString,
    d=l();
    !![];
    )try {
      if(P=parseInt(fv(gw.l) /* "257RaulUz" */)/1*(parseInt(fv(gw.c) /* "1002VJbAHI" */)/2)+-parseInt(fv(gw.d) /* "286266kkIINE" */)/3+-parseInt(fv(gw.P) /* "442788QecTRB" */)/4*(parseInt(fv(gw.R) /* "5ZNAuDJ" */)/5)+parseInt(fv(gw.H) /* "84WLZwMt" */)/6*(parseInt(fv(gw.Z) /* "60032pjHPHf" */)/7)+parseInt(fv(gw.C) /* "8jhTfKQ" */)/8*(-parseInt(fv(gw.O) /* "630342Eotfmp" */)/9)+-parseInt(fv(gw.X) /* "82520cDaZDB" */)/10*(-parseInt(fv(gw.f0) /* "99vPUVil" */)/11)+parseInt(fv(gw.f1) /* "201876oZsoNl" */)/12*(parseInt(fv(gw.f2) /* "52UvhevX" */)/13),
      c===P)break;
      else d.push(d.shift())}
    catch(R) {
      d.push(d.shift())}
  }
  (stringArray,
  114224),
  globalRef=this||self,
  doc=globalRef[decoder(271) /* "document" */],
  deflateCompress=function(gY,
  gq,
  gN,
  gk,
  gE,
  fI,
  l,
  c,
  d,
  P,
  R,
  H,
  Z,
  O,
  X,
  f0) {
    for(gY= {
      l:220,
      c:311,
      d:420,
      P:454,
      R:420,
      H:216}
,
    gq= {
      l:408,
      c:320,
      d:341,
      P:446,
      R:367,
      H:370,
      Z:244,
      C:422,
      O:402,
      X:428,
      f0:392,
      f1:327,
      f2:367}
,
    gN= {
      l:397,
      c:327}
,
    gk= {
      l:408,
      c:320,
      d:367,
      P:341}
,
    gE= {
      l:250,
      c:292}
,
    fI=decoder,
    l= {
      "gypWF":function(f1,
      f2) {
        return f1>f2}
,
      "cyxhk":function(f1,
      f2) {
        return f1<<f2}
,
      "EmJfi":function(f1,
      f2) {
        return f1<f2}
,
      "sAmlv":function(f1,
      f2) {
        return f1<=f2}
,
      "eiYIY":function(f1,
      f2) {
        return f1+f2}
,
      "yEWwH":function(f1,
      f2) {
        return f1<=f2}
,
      "dYEEl":function(f1,
      f2,
      f3) {
        return f1(f2,
        f3)}
,
      "ePjnu":function(f1,
      f2) {
        return f2&f1}
,
      "AxXti":function(f1,
      f2) {
        return f1(f2)}
,
      "ODmrR":function(f1,
      f2) {
        return f2===f1}
,
      "Ewxqb":function(f1,
      f2) {
        return f1+f2}
,
      "LyPqx":function(f1,
      f2) {
        return f1<f2}
,
      "MxOUj":function(f1,
      f2) {
        return f1-f2}
,
      "hIQZR":function(f1,
      f2) {
        return f1-f2}
,
      "JntBN":function(f1,
      f2,
      f3) {
        return f1(f2,
        f3)}
    }
,
    c=[],
    d=[],
    P=[3,
    4,
    5,
    6,
    7,
    8,
    9,
    10,
    11,
    13,
    15,
    17,
    19,
    23,
    27,
    31,
    35,
    43,
    51,
    59,
    67,
    83,
    99,
    115,
    131,
    163,
    195,
    227,
    258],
    R=[0,
    0,
    0,
    0,
    0,
    0,
    0,
    0,
    1,
    1,
    1,
    1,
    2,
    2,
    2,
    2,
    3,
    3,
    3,
    3,
    4,
    4,
    4,
    4,
    5,
    5,
    5,
    5,
    0],
    H=[1,
    2,
    3,
    4,
    5,
    7,
    9,
    13,
    17,
    25,
    33,
    49,
    65,
    97,
    129,
    193,
    257,
    385,
    513,
    769,
    1025,
    1537,
    2049,
    3073,
    4097,
    6145,
    8193,
    12289,
    16385,
    24577],
    Z=[0,
    0,
    0,
    0,
    1,
    1,
    2,
    2,
    3,
    3,
    4,
    4,
    5,
    5,
    6,
    6,
    7,
    7,
    8,
    8,
    9,
    9,
    10,
    10,
    11,
    11,
    12,
    12,
    13,
    13],
    O=0;
    O<288;
    O<144?(X=l[fI(gY.l) /* "Ewxqb" */](48,
    O),
    f0=8):l[fI(gY.c) /* "LyPqx" */](O,
    256)?(X=l[fI(gY.d) /* "MxOUj" */](400+O,
    144),
    f0=9):O<280?(X=l[fI(gY.P) /* "hIQZR" */](O,
    256),
    f0=7):(X=l[fI(gY.R) /* "MxOUj" */](192+O,
    280),
    f0=8),
    c[O]=l[fI(gY.H) /* "JntBN" */](reverseBits,
    X,
    f0),
    d[O]=f0,
    O++);
    return function(f1,
    gx,
    gs,
    fz,
    f2,
    f3,
    f4,
    f5,
    f6,
    f7,
    f8,
    f9,
    fP,
    ft,
    fw,
    fh,
    fb,
    fe,
    fp,
    fA,
    fr,
    fU,
    fG) {
      for(gx= {
        l:397}
,
      gs= {
        l:221,
        c:367,
        d:292,
        P:370,
        R:327,
        H:221,
        Z:367,
        C:392,
        O:446}
,
      fz=fI,
      f2= {
      }
,
      f2[fz(gq.l) /* "AfcKN" */]=function(fJ,
      fm) {
        return fJ<<fm}
,
      f2[fz(gq.c) /* "wKKyr" */]=function(fJ,
      fm) {
        return fJ>=fm}
,
      f2[fz(gq.d) /* "YNtft" */]=function(fJ,
      fm) {
        return fJ&fm}
,
      f3=f2,
      f4=[],
      f5=0,
      f6=0,
      f7=new Int32Array(8192),
      f8=new Int32Array(32768),
      f9=8191,
      emitBits(1,
      1),
      l[fz(gq.P) /* "dYEEl" */](emitBits,
      1,
      2),
      fP=0,
      ft=f1[fz(gq.R) /* "length" */];
      fP<ft;
      ) {
        if(fw=0,
        fh=0,
        l[fz(gq.H) /* "sAmlv" */](fP+3,
        ft)) {
          for(fb=l[fz(gq.Z) /* "AxXti" */](insertMatch,
          fP),
          fe=0;
          fb>=0&&fb<fP&&fP-fb<=32768&&fe<2;
          fe++)for(fU=fz(gq.C) /* "2|1|4|0|3|5" */[fz(gq.O) /* "split" */](`|`),
          fG=0;
          !![];
          ) {
            switch(fU[fG++]) {
              case`0`:for(;
              fA<fp&&l[fz(gq.X) /* "ODmrR" */](f1[fb+fA],
              f1[fP+fA]);
              fA++);
              continue;
              case`1`:fp>258&&(fp=258);
              continue;
              case`2`:fp=ft-fP;
              continue;
              case`3`:fA>fw&&fA>2&&(fw=fA,
              fh=fP-fb,
              fp===fA&&(fe=2));
              continue;
              case`4`:fA=0;
              continue;
              case`5`:fb=f8[fb&32767]-1;
              continue}
            break}
        }
        if(fw>2) {
          for(emitMatch(fw,
          fh),
          fr=1;
          fr<fw&&l[fz(gq.f0) /* "yEWwH" */](l[fz(gq.f1) /* "eiYIY" */](fP+fr,
          3),
          ft);
          insertMatch(fP+fr),
          fr++);
          fP+=fw}
        else emitLiteral(f1[fP++])}
      return l[fz(gq.Z) /* "AxXti" */](emitLiteral,
      256),
      f6>0&&(f4[f4[fz(gq.f2) /* "length" */]]=f5&255),
      f4;
      // deflate: emit the Huffman code for a literal byte
      // emitLiteral -> fg
      function emitLiteral(fJ) {
        emitBits(c[fJ],
        d[fJ])}
      // deflate: bit writer — accumulate bits, flush full bytes to the output
      // emitBits -> ff
      function emitBits(fJ,
      fm,
      fL) {
        for(fL=fz,
        f5|=f3[fL(gk.l) /* "AfcKN" */](fJ,
        f6),
        f6+=fm;
        f3[fL(gk.c) /* "wKKyr" */](f6,
        8);
        f4[f4[fL(gk.d) /* "length" */]]=f3[fL(gk.P) /* "YNtft" */](f5,
        255),
        f5>>>=8,
        f6-=8);
      }
      // deflate: 3-byte rolling hash for LZ77 match lookup
      // hash3 -> fc
      function hash3(fJ,
      fK) {
        return fK=fz,
        l[fK(gx.l) /* "ePjnu" */](f1[fJ+2]^(f1[fJ]<<5.43^f1[fJ+1]<<2),
        f9)>>>0}
      // deflate: insert the current position into the LZ77 hash/prev chain
      // insertMatch -> fd
      function insertMatch(fJ,
      fs,
      fm,
      fT) {
        return fs=fz,
        fm=hash3(fJ),
        fT=f7[fm]-1,
        f8[l[fs(gN.l) /* "ePjnu" */](fJ,
        32767)]=l[fs(gN.c) /* "eiYIY" */](fT,
        1),
        f7[fm]=fJ+1,
        fT}
      // deflate: emit a length/distance code (LZ77 back-reference)
      // emitMatch -> fl
      function emitMatch(fJ,
      fm,
      fk,
      fT,
      fV,
      fj) {
        for(fk=fz,
        fT=0,
        fj=0;
        l[fk(gs.l) /* "EmJfi" */](fT,
        P[fk(gs.c) /* "length" */]);
        fT++)if(fV=P[fT]+l[fk(gs.d) /* "cyxhk" */](1,
        R[fT])-1,
        l[fk(gs.P) /* "sAmlv" */](fJ,
        fV)) {
          fj=fT;
          break}
        for(emitLiteral(l[fk(gs.R) /* "eiYIY" */](257,
        fj)),
        R[fj]&&emitBits(fJ-P[fj],
        R[fj]),
        fT=0;
        l[fk(gs.H) /* "EmJfi" */](fT,
        H[fk(gs.Z) /* "length" */]);
        fT++)if(fV=H[fT]+(1<<Z[fT])-1,
        l[fk(gs.C) /* "yEWwH" */](fm,
        fV)) {
          l[fk(gs.O) /* "dYEEl" */](emitBits,
          l[fk(gs.O) /* "dYEEl" */](reverseBits,
          fT,
          5),
          5),
          Z[fT]&&emitBits(fm-H[fT],
          Z[fT]);
          break}
      }
    }
;
    // bit-reverse (builds the Huffman code table for the deflate compressor)
    // reverseBits -> C
    function reverseBits(f1,
    f2,
    fE,
    f3) {
      for(fE=decodeString,
      f3=0;
      l[fE(gE.l) /* "gypWF" */](f2,
      0);
      f3=l[fE(gE.c) /* "cyxhk" */](f3,
      1)|1.04&f1,
      f1>>>=1,
      f2--);
      return f3}
  }
  (),
  encoderModule=function(ll,
  lg,
  lf,
  l9,
  l8,
  l7,
  l6,
  fx,
  P,
  R,
  f1) {
    return ll= {
      l:280,
      c:243}
,
    lg= {
      l:363,
      c:367,
      d:290,
      P:367,
      R:433}
,
    lf= {
      l:367,
      c:464,
      d:462,
      P:393,
      R:396,
      H:407,
      Z:266,
      C:367,
      O:464,
      X:423,
      f0:226,
      f1:238,
      f2:389,
      f3:396,
      f4:255,
      f5:231}
,
    l9= {
      l:367,
      c:367,
      d:277,
      P:351,
      R:247,
      H:402,
      Z:334,
      C:393,
      O:317,
      X:423,
      f0:334,
      f1:226,
      f2:334,
      f3:358,
      f4:334,
      f5:403,
      f6:319,
      f7:334,
      f8:334,
      f9:403,
      ff:335,
      fg:461}
,
    l8= {
      l:367,
      c:217,
      d:353,
      P:464,
      R:379}
,
    l7= {
      l:317}
,
    l6= {
      l:266,
      c:367,
      d:464,
      P:348,
      R:405}
,
    fx=decoder,
    P= {
      "fCRYV":function(f2,
      f3) {
        return f2<f3}
,
      "QBZau":function(f2,
      f3) {
        return f2===f3}
,
      "JkbfP":function(f2,
      f3) {
        return f2<<f3}
,
      "pjkMt":function(f2,
      f3) {
        return f3^f2}
,
      "nqqfI":function(f2,
      f3) {
        return f2>>>f3}
,
      "RaLgV":function(f2,
      f3) {
        return f2%f3}
,
      "rmhtR":function(f2,
      f3) {
        return f2+f3}
,
      "aJfUr":function(f2,
      f3) {
        return f2/f3}
,
      "mBKdk":fx(ll.l) /* "1|0|3|4|2" */,
      "sUZld":function(f2,
      f3) {
        return f2>>>f3}
,
      "RWPXQ":function(f2,
      f3) {
        return f2+f3}
,
      "EDgeG":function(f2,
      f3) {
        return f2&f3}
,
      "cIxNT":function(f2,
      f3) {
        return f2>>>f3}
,
      "hcFES":function(f2,
      f3) {
        return f2&f3}
,
      "SyheD":function(f2,
      f3) {
        return f2+f3}
,
      "SnyjK":function(f2,
      f3) {
        return f2>>>f3}
,
      "cHtno":function(f2,
      f3) {
        return f2<f3}
,
      "nppWT":function(f2,
      f3) {
        return f2|f3}
,
      "guHLp":function(f2,
      f3) {
        return f2<=f3}
,
      "WKIXS":function(f2,
      f3) {
        return f2>>>f3}
,
      "CHLJd":function(f2,
      f3) {
        return f3&f2}
,
      "RvHuf":function(f2,
      f3) {
        return f3&f2}
,
      "cWwbi":function(f2,
      f3) {
        return f2&f3}
,
      "dwWtY":function(f2,
      f3) {
        return f3==f2}
,
      "nKvxE":function(f2,
      f3) {
        return f2(f3)}
    }
,
    R=`4sfld8jRZW6L0qGn-w5gEKaxMeUzpBhXY1kCr3cIP$QToFum7VND+S9HivOb2AJty`,
    f1= {
    }
,
    f1[fx(ll.c) /* "aHBr2" */]=encodePayload,
    f1;
    // xorshift/wang 32-bit hash mix (x^=x<<13; x^=x>>>17; x^=x<<5)
    // hashMix -> Z
    function hashMix(f2,
    fq) {
      return fq=fx,
      f2^=P[fq(l7.l) /* "JkbfP" */](f2,
      13),
      f2^=f2>>>17,
      f2^=P[fq(l7.l) /* "JkbfP" */](f2,
      5),
      f2>>>.92}
    // XOR stream cipher: keystream = hashMix(fnv1aHash(alphabet)) per position
    // xorCrypt -> C
    function xorCrypt(f2,
    fY,
    f3,
    f4) {
      for(fY=fx,
      f3=fnv1aHash(R),
      f4=0;
      f4<f2[fY(l8.l) /* "length" */];
      f3=hashMix(f3),
      f2[f4]^=P[fY(l8.c) /* "pjkMt" */](P[fY(l8.d) /* "nqqfI" */](f3,
      24),
      R[fY(l8.P) /* "charCodeAt" */](P[fY(l8.R) /* "RaLgV" */](f4,
      64))),
      f4++);
      return f2}
    // UTF-8 encoder (string -> byte array)
    // utf8Encode -> X
    function utf8Encode(f2,
    fi,
    f3,
    f4,
    f5,
    f6,
    f7) {
      for(fi=fx,
      f3=[],
      f4=0,
      f5=0;
      f5<f2[fi(lf.l) /* "length" */];
      f6=f2[fi(lf.c) /* "charCodeAt" */](f5),
      f6<128?f3[f4++]=f6:P[fi(lf.d) /* "cHtno" */](f6,
      2048)?(f3[f4++]=192|P[fi(lf.P) /* "sUZld" */](f6,
      6),
      f3[f4++]=P[fi(lf.R) /* "nppWT" */](128,
      63&f6)):f6>=55296&&P[fi(lf.H) /* "guHLp" */](f6,
      56319)&&P[fi(lf.Z) /* "fCRYV" */](f5+1,
      f2[fi(lf.C) /* "length" */])?(f7=f2[fi(lf.O) /* "charCodeAt" */](++f5),
      f6=P[fi(lf.X) /* "RWPXQ" */](65536+((1023.07&f6)<<10),
      P[fi(lf.f0) /* "EDgeG" */](f7,
      1023)),
      f3[f4++]=240.79|P[fi(lf.f1) /* "WKIXS" */](f6,
      18),
      f3[f4++]=128.26|P[fi(lf.f2) /* "CHLJd" */](f6>>>12,
      63),
      f3[f4++]=P[fi(lf.f3) /* "nppWT" */](128,
      P[fi(lf.f4) /* "RvHuf" */](f6>>>6,
      63)),
      f3[f4++]=128.05|P[fi(lf.f5) /* "cWwbi" */](f6,
      63)):(f3[f4++]=f6>>>12.42|224.11,
      f3[f4++]=63&f6>>>6|128,
      f3[f4++]=128|f6&63.49),
      f5++);
      return f3}
    // base64 encoder, custom alphabet (4sfld8jRZW6L0qGn-…)
    // base64Encode -> O
    function base64Encode(f2,
    fS,
    f3,
    f4,
    f5,
    f6,
    f7,
    f8,
    f9,
    ff,
    fg) {
      for(fS=fx,
      f3=[],
      f4=0,
      f5=f2[fS(l9.l) /* "length" */],
      f6=f5%3,
      f7=f5-f6,
      f3[fS(l9.c) /* "length" */]=P[fS(l9.d) /* "rmhtR" */](P[fS(l9.P) /* "aJfUr" */](f7,
      3)*4,
      f6?f6+1:0),
      f8=0;
      f8<f7;
      f8+=3)for(f9=P[fS(l9.R) /* "mBKdk" */][fS(l9.H) /* "split" */](`|`),
      ff=0;
      !![];
      ) {
        switch(f9[ff++]) {
          case`0`:f3[f4++]=R[fS(l9.Z) /* "charAt" */](P[fS(l9.C) /* "sUZld" */](fg,
          18)&63.97);
          continue;
          case`1`:fg=P[fS(l9.O) /* "JkbfP" */](f2[f8],
          16)|f2[P[fS(l9.d) /* "rmhtR" */](f8,
          1)]<<8|f2[P[fS(l9.X) /* "RWPXQ" */](f8,
          2)];
          continue;
          case`2`:f3[f4++]=R[fS(l9.f0) /* "charAt" */](fg&63.78);
          continue;
          case`3`:f3[f4++]=R[fS(l9.f0) /* "charAt" */](P[fS(l9.f1) /* "EDgeG" */](fg>>>12.5,
          63));
          continue;
          case`4`:f3[f4++]=R[fS(l9.f2) /* "charAt" */](P[fS(l9.f3) /* "cIxNT" */](fg,
          6)&63);
          continue}
        break}
      return f6===1?(fg=f2[f7]<<16.3,
      f3[f4++]=R[fS(l9.f4) /* "charAt" */](P[fS(l9.f5) /* "hcFES" */](fg>>>18.7,
      63)),
      f3[f4++]=R[fS(l9.f0) /* "charAt" */](fg>>>12.65&63.28)):2===f6&&(fg=f2[f7]<<16|f2[P[fS(l9.f6) /* "SyheD" */](f7,
      1)]<<8.66,
      f3[f4++]=R[fS(l9.f7) /* "charAt" */](63&fg>>>18.28),
      f3[f4++]=R[fS(l9.f8) /* "charAt" */](P[fS(l9.f9) /* "hcFES" */](fg>>>12,
      63)),
      f3[f4++]=R[fS(l9.f7) /* "charAt" */](P[fS(l9.ff) /* "SnyjK" */](fg,
      6)&63.74)),
      f3[fS(l9.fg) /* "join" */](``)}
    // payload encoder: utf8 -> (deflate if smaller) -> prefix [253,1,flag] -> xor -> base64
    // encodePayload -> f0
    function encodePayload(f2,
    fF,
    f3,
    f4,
    f5,
    f6) {
      (fF=fx,
      f2=utf8Encode(P[fF(lg.l) /* "dwWtY" */](f2,
      null)?``:f2),
      f3=f2,
      f4=0,
      f2[fF(lg.c) /* "length" */]>=128)&&(f5=P[fF(lg.d) /* "nKvxE" */](deflateCompress,
      f2),
      f5[fF(lg.P) /* "length" */]<f2[fF(lg.c) /* "length" */]&&(f3=f5,
      f4=1));
      return f6=new Uint8Array(f3[fF(lg.c) /* "length" */]+3),
      f6[0]=253,
      f6[1]=1,
      f6[2]=f4,
      f6[fF(lg.R) /* "set" */](f3,
      3),
      base64Encode(P[fF(lg.d) /* "nKvxE" */](xorCrypt,
      f6))}
    // FNV-1a 32-bit hash (2166136261, imul(x,16777619))
    // fnv1aHash -> H
    function fnv1aHash(f2,
    fN,
    f3,
    f4) {
      for(fN=fx,
      f3=2166136261,
      f4=0;
      P[fN(l6.l) /* "fCRYV" */](f4,
      f2[fN(l6.c) /* "length" */]);
      f3=(f3^=f2[fN(l6.d) /* "charCodeAt" */](f4),
      Math[fN(l6.P) /* "imul" */](f3,
      16777619)>>>0),
      f4++);
      return P[fN(l6.R) /* "QBZau" */](f3,
      0)?2779062077:f3}
  }
  (),
  typeCodes= {
  }
,
  typeCodes[decoder(347) /* "object" */]=`o`,
  typeCodes[decoder(235) /* "string" */]=`s`,
  typeCodes[decoder(406) /* "undefined" */]=`u`,
  typeCodes[decoder(293) /* "symbol" */]=`z`,
  typeCodes[decoder(256) /* "number" */]=`n`,
  typeCodes[decoder(451) /* "bigint" */]=`I`,
  typeCode=typeCodes,
  // props enumerator (b.xixz7): walk an object's proto-chain, classify each value, collect `prefix.prop` -> type
  globalRef[decoder(294) /* "xixz7" */]=function(P,
  R,
  H,
  Z,
  lJ,
  lG,
  lU,
  fQ,
  C,
  X,
  f0,
  f1,
  f2,
  f3,
  f4,
  f5) {
    if(lJ= {
      l:309,
      c:449,
      d:273,
      P:296,
      R:430,
      H:384,
      Z:364,
      C:236,
      O:364,
      X:248,
      f0:401,
      f1:367,
      f2:339,
      f3:427,
      f4:369}
,
    lG= {
      l:316,
      c:367,
      d:322,
      P:225}
,
    lU= {
      l:365,
      c:459,
      d:425,
      P:439}
,
    fQ=decoder,
    C= {
      "gmCPd":function(f6,
      f7) {
        return f6+f7}
,
      "pyqSM":function(f6,
      f7) {
        return f6(f7)}
,
      "VePCj":function(f6,
      f7) {
        return f6===f7}
,
      "GEYGP":fQ(lJ.l) /* "d.cookie" */,
      "Hgivi":function(f6,
      f7,
      f8) {
        return f6(f7,
        f8)}
    }
,
    R===null||R===void 0)return Z;
    for(X=C[fQ(lJ.c) /* "pyqSM" */](walkProtoChain,
    R),
    P[fQ(lJ.d) /* "Object" */][fQ(lJ.P) /* "getOwnPropertyNames" */]&&(X=X[fQ(lJ.R) /* "concat" */](P[fQ(lJ.d) /* "Object" */][fQ(lJ.P) /* "getOwnPropertyNames" */](R))),
    X=P[fQ(lJ.H) /* "Array" */][fQ(lJ.Z) /* "from" */]&&P[fQ(lJ.C) /* "Set" */]?P[fQ(lJ.H) /* "Array" */][fQ(lJ.O) /* "from" */](new P[fQ(lJ.C) /* "Set" */](X)):function(f6,
    fB,
    f7) {
      for(fB=fQ,
      f6[fB(lG.l) /* "sort" */](),
      f7=0;
      f7<f6[fB(lG.c) /* "length" */];
      f6[f7]===f6[C[fB(lG.d) /* "gmCPd" */](f7,
      1)]?f6[fB(lG.P) /* "splice" */](f7+1,
      1):f7+=1);
      return f6}
    (X),
    f0=`nAsAa`.split(`A`),
    f0=f0[fQ(lJ.X) /* "includes" */][fQ(lJ.f0) /* "bind" */](f0),
    f1=0;
    f1<X[fQ(lJ.f1) /* "length" */];
    f1++) {
      f3=(f2=X[f1],
      H+f2);
      try {
        f4=R[f2],
        f5=classifyValue(P,
        f4),
        f0(f5)?(f2=+f4,
        f2=f5===`s`&&C[fQ(lJ.f2) /* "VePCj" */](f2,
        f2),
        C[fQ(lJ.f2) /* "VePCj" */](f3,
        C[fQ(lJ.f3) /* "GEYGP" */])?C[fQ(lJ.f4) /* "Hgivi" */](collectProp,
        f3,
        f5):f2||collectProp(f3,
        f4)):collectProp(f3,
        f5)}
      catch(f6) {
        C[fQ(lJ.f4) /* "Hgivi" */](collectProp,
        f3,
        `i`)}
    }
    return Z;
    // append a classified prop to the collected map
    // collectProp -> O
    function collectProp(f6,
    f7,
    fu) {
      fu=fQ,
      Object[fu(lU.l) /* "prototype" */][fu(lU.c) /* "hasOwnProperty" */][fu(lU.d) /* "call" */](Z,
      f7)||(Z[f7]=[]),
      Z[f7][fu(lU.P) /* "push" */](f6)}
  }
,
  messageTypes=[decoder(224) /* "_cf_chl_opt" */,
  decoder(374) /* "_cf_chl_state" */,
  decoder(229) /* "RbzKV2" */,
  decoder(321) /* "AMTP9" */,
  decoder(382) /* "lwyw2" */,
  decoder(337) /* "GJAhI4" */,
  decoder(380) /* "FZOf6" */,
  decoder(415) /* "RItcy2" */,
  decoder(346) /* "aQQUn1" */,
  decoder(404) /* "mlyM5" */,
  decoder(373) /* "zFdYF4" */,
  decoder(274) /* "qQFlt0" */,
  decoder(237) /* "yCCo2" */,
  decoder(378) /* "WhBwu7" */,
  decoder(267) /* "phPfe0" */,
  decoder(276) /* "ANTT9" */,
  decoder(294) /* "xixz7" */,
  decoder(314) /* "mUKI2" */,
  decoder(253) /* "KBTt2" */,
  decoder(440) /* "IfWx3" */,
  decoder(246) /* "PnHD6" */],
  isMessageType=messageTypes[decoder(248) /* "includes" */][decoder(401) /* "bind" */](messageTypes),
  // update dispatcher (b.mUKI2): fold a message's prop lists into the collected map, skipping _cf_chl_* keys
  globalRef[decoder(314) /* "mUKI2" */]=function(R,
  H,
  lT,
  fM,
  Z,
  C,
  O,
  X,
  f0,
  f1,
  f2,
  f3) {
    for(lT= {
      l:419,
      c:445,
      d:367,
      P:419,
      R:249,
      H:439}
,
    fM=decoder,
    Z= {
    }
,
    Z[fM(lT.l) /* "TNtgO" */]=function(f4,
    f5) {
      return f4!==f5}
,
    C=Z,
    O=Object[fM(lT.c) /* "keys" */](H),
    X=0;
    X<O[fM(lT.d) /* "length" */];
    X++)for(f0=O[X],
    f1=f0===`f`?`N`:f0,
    f1=R[f1]||(R[f1]=[]),
    f0=H[f0],
    f2=0;
    f2<f0[fM(lT.d) /* "length" */];
    f3=f0[f2],
    C[fM(lT.P) /* "TNtgO" */](f1[fM(lT.R) /* "indexOf" */](f3),
    -1)||isMessageType(f3)||f1[fM(lT.H) /* "push" */](`o.`+f3),
    f2++);
  }
,
  pollIntervalMs=30,
  pollTimer=null,
  hasState=![],
  globalRef[decoder(381) /* "HkQGj2" */]=typeof globalRef[decoder(381) /* "HkQGj2" */]===decoder(298) /* "function" */?globalRef[decoder(381) /* "HkQGj2" */]:function() {
  }
,
  globalRef[decoder(340) /* "Aclqb0" */]=typeof globalRef[decoder(340) /* "Aclqb0" */]===decoder(298) /* "function" */?globalRef[decoder(340) /* "Aclqb0" */]:function(l) {
  }
,
  challengeOpts=challengeParams(),
  intervalState= {
    "interval":clampInterval(challengeOpts&&challengeOpts.i),
    "updates":0}
,
  globalRef[decoder(374) /* "_cf_chl_state" */]&&(hasState=!![],
  intervalState=globalRef[decoder(374) /* "_cf_chl_state" */],
  delete globalRef[decoder(374) /* "_cf_chl_state" */],
  intervalState[decoder(269) /* "updates" */]=intervalState[decoder(269) /* "updates" */]||0),
  submitOneshot=typeof submitOneshot===decoder(298) /* "function" */?submitOneshot:function(l,
  c,
  c6,
  c5,
  c4,
  c3,
  c0,
  lX,
  g4,
  d,
  P,
  R,
  H,
  Z,
  C,
  O,
  X) {
    for(c6= {
      l:289,
      c:260,
      d:326,
      P:402,
      R:303,
      H:243,
      Z:463,
      C:260,
      O:410,
      X:300,
      f0:224,
      f1:295,
      f2:227,
      f3:215,
      f4:215,
      f5:218,
      f6:366,
      f7:340,
      f8:352,
      f9:426,
      ff:287,
      fg:383,
      fl:395,
      fc:251,
      fd:386}
,
    c5= {
      l:330,
      c:270}
,
    c4= {
      l:330,
      c:350}
,
    c3= {
      l:388,
      c:375,
      d:388,
      P:336,
      R:431,
      H:367,
      Z:259,
      C:381,
      O:391,
      X:258,
      f0:275}
,
    c0= {
      l:450}
,
    lX= {
      l:357}
,
    g4=decoder,
    d= {
      "uMNNs":g4(c6.l) /* "/cdn-cgi/challenge-platform/h/" */,
      "VAePU":function(f0) {
        return f0()}
,
      "YNhUH":function(f0,
      f1) {
        return f0(f1)}
,
      "XmFne":g4(c6.c) /* "timeout" */,
      "SrJsV":function(f0,
      f1) {
        return f0<f1}
    }
,
    P=g4(c6.d) /* "8|13|3|2|11|1|12|9|10|5|7|4|6|0" */[g4(c6.P) /* "split" */](`|`),
    R=0;
    !![];
    ) {
      switch(P[R++]) {
        case`0`:H[g4(c6.R) /* "send" */](encoderModule[g4(c6.H) /* "aHBr2" */](JSON[g4(c6.Z) /* "stringify" */](C)));
        continue;
        case`1`:H[g4(c6.C) /* "timeout" */]=5e3;
        continue;
        case`2`:H=new globalRef[g4(c6.O) /* "XMLHttpRequest" */];
        continue;
        case`3`:Z=d[g4(c6.X) /* "uMNNs" */]+globalRef[g4(c6.f0) /* "_cf_chl_opt" */][g4(c6.f1) /* "STupN6" */]+`/jsd/oneshot/aae2b9a1c261/0.04746454347771223:1786791917:SI2K2foUc3vriBuvjfQ9BbgWqqVIO7damTJOoppKeJ8/`+X.r;
        continue;
        case`4`:X.ut&&(C[`ut`]=X.ut);
        continue;
        case`5`:C= {
          "t":challengeTimestamp(),
          "lhr":doc[g4(c6.f2) /* "location" */]&&doc[g4(c6.f2) /* "location" */][g4(c6.f3) /* "href" */]?doc[g4(c6.f2) /* "location" */][g4(c6.f4) /* "href" */]:``,
          "api":X[g4(c6.f5) /* "api" */]?!![]:![],
          "c":d[g4(c6.f6) /* "VAePU" */](shouldPoll),
          "payload":l}
;
        continue;
        case`6`:globalRef[g4(c6.f7) /* "Aclqb0" */](C);
        continue;
        case`7`:X.u&&(C[`u`]=X.u);
        continue;
        case`8`:O= {
          "nuKlC":function(f0,
          f1,
          g5) {
            return g5=g4,
            d[g5(lX.l) /* "YNhUH" */](f0,
            f1)}
,
          "ORZFo":d[g4(c6.f8) /* "XmFne" */],
          "TeryN":function(f0,
          f1,
          g6) {
            return g6=g4,
            d[g6(c0.l) /* "SrJsV" */](f0,
            f1)}
,
          "riphT":function(f0,
          f1) {
            return f0>f1}
,
          "dsHHY":g4(c6.f9) /* "success" */,
          "GNWmp":function(f0,
          f1) {
            return f0(f1)}
        }
;
        continue;
        case`9`:H[g4(c6.ff) /* "onload" */]=function(g7,
        f0,
        f1) {
          if(g7=g4,
          H[g7(c3.l) /* "status" */]>=200&&O[g7(c3.c) /* "TeryN" */](H[g7(c3.d) /* "status" */],
          300)) {
            try {
              f1=H[g7(c3.P) /* "responseText" */],
              f1&&O[g7(c3.R) /* "riphT" */](f1[g7(c3.H) /* "length" */],
              0)&&(f0=JSON[g7(c3.Z) /* "parse" */](f1))}
            catch(f2) {
            }
            globalRef[g7(c3.C) /* "HkQGj2" */](),
            c(O[g7(c3.O) /* "dsHHY" */],
            f0)}
          else O[g7(c3.X) /* "GNWmp" */](c,
          g7(c3.f0) /* "http-code:" */+H[g7(c3.l) /* "status" */])}
;
        continue;
        case`10`:H[g4(c6.fg) /* "onerror" */]=function(g8) {
          g8=g4,
          O[g8(c4.l) /* "nuKlC" */](c,
          g8(c4.c) /* "xhr-error" */)}
;
        continue;
        case`11`:H[g4(c6.fl) /* "open" */](g4(c6.fc) /* "POST" */,
        Z);
        continue;
        case`12`:H[g4(c6.fd) /* "ontimeout" */]=function(g9) {
          g9=g4,
          O[g9(c5.l) /* "nuKlC" */](c,
          O[g9(c5.c) /* "ORZFo" */])}
;
        continue;
        case`13`:X=challengeParams();
        continue}
      break}
  }
,
  M=randomUuid(),
  bootstrap();
  // challenge params: window.__CF$cv$params or _cf_chl_opt.pp
  // challengeParams -> s
  function challengeParams(lN,
  fZ) {
    return lN= {
      l:456,
      c:224}
,
    fZ=decoder,
    globalRef[fZ(lN.l) /* "__CF$cv$params" */]||globalRef[fZ(lN.c) /* "_cf_chl_opt" */]&&globalRef[fZ(lN.c) /* "_cf_chl_opt" */].pp}
  // classify a fingerprint value -> type code (o/s/n/I/z/u/x/p/a/D/T/F + N native vs f function)
  // classifyValue -> J
  function classifyValue(c,
  d,
  lh,
  fy,
  P,
  R,
  H) {
    if(lh= {
      l:213,
      c:252,
      d:371,
      P:421,
      R:213,
      H:347,
      Z:278,
      C:242,
      O:384,
      X:458,
      f0:252,
      f1:384,
      f2:443,
      f3:298,
      f4:371,
      f5:323,
      f6:421,
      f7:323,
      f8:365,
      f9:385,
      ff:425,
      fg:249,
      fl:304}
,
    fy=decoder,
    P= {
    }
,
    P[fy(lh.l) /* "lZtUq" */]=function(Z,
    C) {
      return Z==C}
,
    P[fy(lh.c) /* "oCDiW" */]=function(Z,
    C) {
      return C===Z}
,
    P[fy(lh.d) /* "ZgqkN" */]=function(Z,
    C) {
      return Z instanceof C}
,
    P[fy(lh.P) /* "elFLS" */]=function(Z,
    C) {
      return Z>C}
,
    R=P,
    R[fy(lh.R) /* "lZtUq" */](d,
    null))return R[fy(lh.c) /* "oCDiW" */](d,
    void 0)?`u`:`x`;
    if(H=typeof d,
    H===fy(lh.H) /* "object" */)try {
      if(c[fy(lh.Z) /* "Promise" */]&&d instanceof c[fy(lh.Z) /* "Promise" */])return d[fy(lh.C) /* "catch" */](function() {
      }
      ),
      `p`}
    catch(Z) {
    }
    return c[fy(lh.O) /* "Array" */][fy(lh.X) /* "isArray" */](d)?`a`:R[fy(lh.f0) /* "oCDiW" */](d,
    c[fy(lh.f1) /* "Array" */])?String[fy(lh.f2) /* "fromCharCode" */](68):!0===d?`T`:R[fy(lh.c) /* "oCDiW" */](d,
    !1)?`F`:H==fy(lh.f3) /* "function" */?R[fy(lh.f4) /* "ZgqkN" */](d,
    c[fy(lh.f5) /* "Function" */])&&R[fy(lh.f6) /* "elFLS" */](c[fy(lh.f7) /* "Function" */][fy(lh.f8) /* "prototype" */][fy(lh.f9) /* "toString" */][fy(lh.ff) /* "call" */](d)[fy(lh.fg) /* "indexOf" */](fy(lh.fl) /* "[native code]" */),
    0)?`N`:`f`:typeCode[H]||`?`}
  // string array builder: one semicolon-delimited string, split on ';' (252 entries)
  // stringArray -> f
  function stringArray(cp) {
    return cp=`timeout;RVSsc;addEventListener;fnQgW;hdChW;jsd;fCRYV;phPfe0;_cb;updates;ORZFo;document;nonce;Object;qQFlt0;http-code:;ANTT9;rmhtR;Promise;interval;1|0|3|4|2;loading;TWfR8;Twavn2;1002VJbAHI;GcIeO;enZML;onload;DQLGX;/cdn-cgi/challenge-platform/h/;nKvxE;postMessage;cyxhk;symbol;xixz7;STupN6;getOwnPropertyNames;201876oZsoNl;function;source;uMNNs;Acqye;clientInformation;send;[native code];floor;rOIEM3;searchParams;blUGo;d.cookie;cloudflare-invisible;LyPqx;WAiB1;ZSOv1;mUKI2;630342Eotfmp;sort;JkbfP;parent;SyheD;wKKyr;AMTP9;gmCPd;Function;randomUUID;onreadystatechange;8|13|3|2|11|1|12|9|10|5|7|4|6|0;eiYIY;YpZj8;appendChild;nuKlC;now;contentDocument;442788QecTRB;charAt;SnyjK;responseText;GJAhI4;aYzwh;VePCj;Aclqb0;YNtft;body;event;99vPUVil;RBphY;aQQUn1;object;imul;parentNode;xhr-error;aJfUr;XmFne;nqqfI;ReRjJ;/jsd;MJLB4;YNhUH;cIxNT;test;6|2|4|1|5|0|3;LuCOq;zxpwE;dwWtY;from;prototype;VAePU;length;ZNvtZ;Hgivi;sAmlv;ZgqkN;shouldUpdate;zFdYF4;_cf_chl_state;TeryN;MuzPF;script;WhBwu7;RaLgV;FZOf6;HkQGj2;lwyw2;onerror;Array;toString;ontimeout;iframe;status;CHLJd;DOMContentLoaded;dsHHY;yEWwH;sUZld;60032pjHPHf;open;nppWT;ePjnu;fqAao;84WLZwMt;7|3|9|13|10|8|11|6|4|12|5|0|2|1;bind;split;hcFES;mlyM5;QBZau;undefined;guHLp;AfcKN;readyState;XMLHttpRequest;oXGcb;detail;getPrototypeOf;ndoPZ;RItcy2;NZxYc;UVQbE7;52UvhevX;TNtgO;MxOUj;elFLS;2|1|4|0|3|5;RWPXQ;qWaRi;call;success;GEYGP;ODmrR;navigator;concat;riphT;removeChild;set;LjQem;82520cDaZDB;getElementsByTagName;cJGCD;zTZz2;push;IfWx3;AMWSl;tlbLb;fromCharCode;error on cf_chl_props;keys;dYEEl;sid;replaceChild;pyqSM;SrJsV;bigint;286266kkIINE;random;hIQZR;error;__CF$cv$params;contentWindow;isArray;hasOwnProperty;8jhTfKQ;join;cHtno;stringify;charCodeAt;lZtUq;YcuVP;href;JntBN;pjkMt;api;sJcj4;Ewxqb;EmJfi;5ZNAuDJ;tabIndex;_cf_chl_opt;splice;EDgeG;location;intervalUpdated;RbzKV2;src;cWwbi;display: none;cKJIQ;style;string;Set;yCCo2;WKIXS;createElement;async;arRwm;catch;aHBr2;AxXti;257RaulUz;PnHD6;mBKdk;includes;indexOf;gypWF;POST;oCDiW;KBTt2;xGpNZ;RvHuf;number;zYyq2;GNWmp;parse`.split(`;`),
    stringArray=function() {
      return cp}
,
    stringArray()}
  // DOMContentLoaded bootstrap: wire the fresh-iframe fingerprint sample + challenge flow
  // bootstrap -> D
  function bootstrap(cb,
  ch,
  cw,
  cP,
  gl,
  l,
  c,
  d,
  P,
  R,
  H,
  Z,
  C) {
    for(cb= {
      l:390,
      c:360,
      d:402,
      P:456,
      R:338,
      H:409,
      Z:281,
      C:262,
      O:262,
      X:416,
      f0:325,
      f1:325}
,
    ch= {
      l:368}
,
    cw= {
      l:409,
      c:281,
      d:325}
,
    cP= {
      l:376}
,
    gl=decoder,
    l= {
      "aYzwh":function(O,
      X) {
        return X!==O}
,
      "NZxYc":gl(cb.l) /* "DOMContentLoaded" */,
      "ZNvtZ":function(O) {
        return O()}
    }
,
    c=gl(cb.c) /* "6|2|4|1|5|0|3" */[gl(cb.d) /* "split" */](`|`),
    d=0;
    !![];
    ) {
      switch(c[d++]) {
        case`0`:P=function(gc) {
          if(gc=gl,
          !Z) {
            if(Z=!![],
            !isChallengeFresh())return;
            hasState?C[gc(cP.l) /* "MuzPF" */](schedulePoll):runChallenge(function(O) {
              postToParent(R,
              O)}
            )}
        }
;
        continue;
        case`1`:if(!isChallengeFresh())return;
        continue;
        case`2`:R=globalRef[gl(cb.P) /* "__CF$cv$params" */];
        continue;
        case`3`:l[gl(cb.R) /* "aYzwh" */](doc[gl(cb.H) /* "readyState" */],
        gl(cb.Z) /* "loading" */)?P():globalRef[gl(cb.C) /* "addEventListener" */]?doc[gl(cb.O) /* "addEventListener" */](l[gl(cb.X) /* "NZxYc" */],
        P):(H=doc[gl(cb.f0) /* "onreadystatechange" */]||function() {
        }
,
        doc[gl(cb.f1) /* "onreadystatechange" */]=function(gd) {
          gd=gl,
          H(),
          doc[gd(cw.l) /* "readyState" */]!==gd(cw.c) /* "loading" */&&(doc[gd(cw.d) /* "onreadystatechange" */]=H,
          P())}
        );
        continue;
        case`4`:if(!R)return;
        continue;
        case`5`:Z=![];
        continue;
        case`6`:C= {
          "MuzPF":function(O,
          gP) {
            return gP=gl,
            l[gP(ch.l) /* "ZNvtZ" */](O)}
        }
;
        continue}
      break}
  }
  // run one challenge cycle: sample, submit, reschedule on interval/shouldUpdate
  // runChallenge -> L
  function runChallenge(l,
  lL,
  lz,
  fD,
  c,
  d) {
    lL= {
      l:254,
      c:444}
,
    lz= {
      l:263,
      c:228,
      d:298,
      P:372,
      R:254}
,
    fD=decoder,
    c= {
      "fnQgW":function(P,
      R) {
        return P(R)}
,
      "xGpNZ":function(P) {
        return P()}
    }
,
    schedulePoll(),
    d=c[fD(lL.l) /* "xGpNZ" */](sampleFingerprint),
    submitSolve(d.r,
    function(P,
    R,
    fo,
    H) {
      fo=fD,
      H=c[fo(lz.l) /* "fnQgW" */](applyUpdate,
      R),
      H[fo(lz.c) /* "intervalUpdated" */]&&schedulePoll(),
      typeof l===fo(lz.d) /* "function" */&&l(P),
      H[fo(lz.P) /* "shouldUpdate" */]&&shouldPoll()&&c[fo(lz.R) /* "xGpNZ" */](refreshChallenge)}
    ),
    d.e&&submitEventBeacon(fD(lL.c) /* "error on cf_chl_props" */,
    d.e)}
  // locate the challenge <script> element whose src matches …/challenge-platform/…main.js
  // findChallengeScript -> q
  function findChallengeScript(ly,
  fO,
  c,
  d,
  P,
  R,
  H) {
    for(ly= {
      l:434,
      c:377,
      d:308,
      P:436,
      R:434,
      H:308,
      Z:367,
      C:230,
      O:359}
,
    fO=decoder,
    c= {
    }
,
    c[fO(ly.l) /* "LjQem" */]=fO(ly.c) /* "script" */,
    c[fO(ly.d) /* "blUGo" */]=function(Z,
    C) {
      return Z<C}
,
    d=c,
    P=doc[fO(ly.P) /* "getElementsByTagName" */](d[fO(ly.R) /* "LjQem" */]),
    R=/\/cdn-cgi\/challenge-platform\/(?:h\/[^/]+\/)?scripts\/(?:jsd|precursor)(?:\/[^/]+)?\/main\.js/,
    H=0;
    d[fO(ly.H) /* "blUGo" */](H,
    P[fO(ly.Z) /* "length" */]);
    H++)if(P[H][fO(ly.C) /* "src" */]&&R[fO(ly.O) /* "test" */](P[H][fO(ly.C) /* "src" */]))return P[H];
    return null}
  // true while the challenge should keep polling (no api flag, interval > 0)
  // shouldPoll -> K
  function shouldPoll(lx,
  fH,
  c,
  d,
  P) {
    return lx= {
      l:233,
      c:218,
      d:279}
,
    fH=decoder,
    c= {
    }
,
    c[fH(lx.l) /* "cKJIQ" */]=function(R,
    H) {
      return R>H}
,
    d=c,
    P=challengeParams(),
    P&&P[fH(lx.c) /* "api" */]?![]:d[fH(lx.l) /* "cKJIQ" */](intervalState[fH(lx.d) /* "interval" */],
    0)}
  // clamp: return x if it's a number >= pollIntervalMs, else 0
  // clampInterval -> k
  function clampInterval(c,
  lK,
  fR,
  d,
  P) {
    return lK= {
      l:441,
      c:441,
      d:256}
,
    fR=decoder,
    d= {
    }
,
    d[fR(lK.l) /* "AMWSl" */]=function(R,
    H) {
      return R===H}
,
    P=d,
    P[fR(lK.c) /* "AMWSl" */](typeof c,
    fR(lK.d) /* "number" */)&&c>=pollIntervalMs?c:0}
  // POST the collected props to the /eb event-beacon endpoint
  // submitEventBeacon -> W
  function submitEventBeacon(P,
  R,
  cg,
  gg,
  H,
  Z,
  C,
  O,
  X,
  f0,
  f1,
  f2,
  f3) {
    if(cg= {
      l:257,
      c:438,
      d:345,
      P:289,
      R:224,
      H:295,
      Z:355,
      C:410,
      O:395,
      X:251,
      f0:260,
      f1:386,
      f2:313,
      f3:224,
      f4:219,
      f5:219,
      f6:312,
      f7:312,
      f8:283,
      f9:356,
      ff:306,
      fg:282,
      fl:417,
      fc:328,
      fd:265,
      fP:303,
      ft:243,
      fw:463}
,
    gg=decoder,
    H= {
      "RBphY":function(f4) {
        return f4()}
    }
,
    !randomChance(.001))return![];
    C=(Z= {
    }
,
    Z[gg(cg.l) /* "zYyq2" */]=P,
    Z[gg(cg.c) /* "zTZz2" */]=R,
    Z);
    try {
      O=H[gg(cg.d) /* "RBphY" */](challengeParams),
      X=gg(cg.P) /* "/cdn-cgi/challenge-platform/h/" */+globalRef[gg(cg.R) /* "_cf_chl_opt" */][gg(cg.H) /* "STupN6" */]+`/eb/0.04746454347771223:1786791917:SI2K2foUc3vriBuvjfQ9BbgWqqVIO7damTJOoppKeJ8/`+O.r+gg(cg.Z) /* "/jsd" */,
      f0=new globalRef[gg(cg.C) /* "XMLHttpRequest" */],
      f0[gg(cg.O) /* "open" */](gg(cg.X) /* "POST" */,
      X),
      f0[gg(cg.f0) /* "timeout" */]=2500,
      f0[gg(cg.f1) /* "ontimeout" */]=function() {
      }
,
      f1= {
      }
,
      f1[gg(cg.f2) /* "ZSOv1" */]=globalRef[gg(cg.f3) /* "_cf_chl_opt" */][gg(cg.f2) /* "ZSOv1" */],
      f1[gg(cg.f4) /* "sJcj4" */]=globalRef[gg(cg.R) /* "_cf_chl_opt" */][gg(cg.f5) /* "sJcj4" */],
      f1[gg(cg.f6) /* "WAiB1" */]=globalRef[gg(cg.f3) /* "_cf_chl_opt" */][gg(cg.f7) /* "WAiB1" */],
      f1[gg(cg.f8) /* "Twavn2" */]=globalRef[gg(cg.R) /* "_cf_chl_opt" */][gg(cg.f9) /* "MJLB4" */],
      f1[gg(cg.ff) /* "rOIEM3" */]=M,
      f2=f1,
      f3= {
      }
,
      f3[gg(cg.fg) /* "TWfR8" */]=C,
      f3[gg(cg.fl) /* "UVQbE7" */]=f2,
      f3[gg(cg.fc) /* "YpZj8" */]=gg(cg.fd) /* "jsd" */,
      f0[gg(cg.fP) /* "send" */](encoderModule[gg(cg.ft) /* "aHBr2" */](JSON[gg(cg.fw) /* "stringify" */](f3)))}
    catch(f4) {
    }
  }
  // challenge issued-at timestamp: floor(+atob(params.t))
  // challengeTimestamp -> F
  function challengeTimestamp(lo,
  g2,
  l) {
    return lo= {
      l:305}
,
    g2=decoder,
    l=challengeParams(),
    Math[g2(lo.l) /* "floor" */](+atob(l.t))}
  // parse an update message -> { intervalUpdated, shouldUpdate }
  // applyUpdate -> N
  function applyUpdate(c,
  li,
  fC,
  d,
  P,
  R,
  H) {
    if(li= {
      l:228,
      c:372,
      d:264,
      P:347,
      R:411,
      H:424,
      Z:279}
,
    fC=decoder,
    d= {
      "hdChW":function(Z) {
        return Z()}
,
      "oXGcb":function(Z,
      C) {
        return Z===C}
,
      "qWaRi":function(Z,
      C) {
        return Z!==C}
    }
,
    P= {
    }
,
    P[fC(li.l) /* "intervalUpdated" */]=![],
    P[fC(li.c) /* "shouldUpdate" */]=![],
    R=P,
    !d[fC(li.d) /* "hdChW" */](shouldPoll))return R;
    if(!c||typeof c!==fC(li.P) /* "object" */)return R;
    (d[fC(li.R) /* "oXGcb" */](c.u,
    !![])&&(R[fC(li.c) /* "shouldUpdate" */]=!![]),
    d[fC(li.H) /* "qWaRi" */](c.i,
    undefined))&&(H=clampInterval(c.i),
    H!==intervalState[fC(li.Z) /* "interval" */]&&(intervalState[fC(li.Z) /* "interval" */]=H,
    R[fC(li.l) /* "intervalUpdated" */]=!![]));
    return R}
  // string-array decoder: stringArray()[arg-213]
  // decodeString -> g
  function decodeString(l,
  c,
  d,
  P) {
    return l=l-213,
    d=stringArray(),
    P=d[l],
    P}
  // submit the solve (thin wrapper over submitOneshot)
  // submitSolve -> Q
  function submitSolve(l,
  c) {
    submitOneshot(l,
    c)}
  // postMessage the result (source:cloudflare-invisible) to the parent frame
  // postToParent -> o
  function postToParent(P,
  R,
  ce,
  gt,
  H,
  Z,
  C,
  O) {
    if(ce= {
      l:301,
      c:426,
      d:285,
      P:310,
      R:218,
      H:301,
      Z:299,
      C:447,
      O:343,
      X:318,
      f0:291,
      f1:299,
      f2:310,
      f3:447,
      f4:343,
      f5:455,
      f6:412}
,
    gt=decoder,
    H= {
    }
,
    H[gt(ce.l) /* "Acqye" */]=gt(ce.c) /* "success" */,
    H[gt(ce.d) /* "GcIeO" */]=gt(ce.P) /* "cloudflare-invisible" */,
    Z=H,
    !P[gt(ce.R) /* "api" */])return;
    R===Z[gt(ce.H) /* "Acqye" */]?(C= {
    }
,
    C[gt(ce.Z) /* "source" */]=Z[gt(ce.d) /* "GcIeO" */],
    C[gt(ce.C) /* "sid" */]=P.r,
    C[gt(ce.O) /* "event" */]=Z[gt(ce.l) /* "Acqye" */],
    globalRef[gt(ce.X) /* "parent" */][gt(ce.f0) /* "postMessage" */](C,
    `*`)):(O= {
    }
,
    O[gt(ce.f1) /* "source" */]=gt(ce.f2) /* "cloudflare-invisible" */,
    O[gt(ce.f3) /* "sid" */]=P.r,
    O[gt(ce.f4) /* "event" */]=gt(ce.f5) /* "error" */,
    O[gt(ce.f6) /* "detail" */]=R,
    globalRef[gt(ce.X) /* "parent" */][gt(ce.f0) /* "postMessage" */](O,
    `*`))}
  // sample a FRESH iframe's window/navigator/document property surface (the fingerprint)
  // sampleFingerprint -> j
  function sampleFingerprint(lj,
  fW,
  d,
  P,
  R,
  H,
  Z,
  C) {
    d=(lj= {
      l:232,
      c:302,
      d:429,
      P:332,
      R:239,
      H:387,
      Z:234,
      C:442,
      O:223,
      X:342,
      f0:329,
      f1:457,
      f2:361,
      f3:414,
      f4:362,
      f5:398,
      f6:342,
      f7:432}
,
    fW=decoder,
    {
      "tlbLb":fW(lj.l) /* "display: none" */,
      "LuCOq":function(O,
      X,
      f0,
      f1,
      f2) {
        return O(X,
        f0,
        f1,
        f2)}
,
      "ndoPZ":fW(lj.c) /* "clientInformation" */,
      "zxpwE":fW(lj.d) /* "navigator" */,
      "fqAao":fW(lj.P) /* "contentDocument" */}
    );
    try {
      return P=doc[fW(lj.R) /* "createElement" */](fW(lj.H) /* "iframe" */),
      P[fW(lj.Z) /* "style" */]=d[fW(lj.C) /* "tlbLb" */],
      P[fW(lj.O) /* "tabIndex" */]=`-1`,
      doc[fW(lj.X) /* "body" */][fW(lj.f0) /* "appendChild" */](P),
      R=P[fW(lj.f1) /* "contentWindow" */],
      H= {
      }
,
      H=d[fW(lj.f2) /* "LuCOq" */](xixz7,
      R,
      R,
      ``,
      H),
      H=xixz7(R,
      R[d[fW(lj.f3) /* "ndoPZ" */]]||R[d[fW(lj.f4) /* "zxpwE" */]],
      `n.`,
      H),
      H=xixz7(R,
      P[d[fW(lj.f5) /* "fqAao" */]],
      `d.`,
      H),
      doc[fW(lj.f6) /* "body" */][fW(lj.f7) /* "removeChild" */](P),
      Z= {
      }
,
      Z[`r`]=H,
      Z[`e`]=null,
      Z}
    catch(O) {
      return C= {
      }
,
      C[`r`]= {
      }
,
      C[`e`]=O,
      C}
  }
  // crypto.randomUUID() or empty string
  // randomUuid -> B
  function randomUuid(c8,
  gf) {
    return c8= {
      l:324}
,
    gf=decoder,
    crypto&&crypto[gf(c8.l) /* "randomUUID" */]?crypto[gf(c8.l) /* "randomUUID" */]():``}
  // schedule the next runChallenge after pollIntervalMs
  // schedulePoll -> S
  function schedulePoll(lW,
  g0) {
    if(lW= {
      l:279}
,
    g0=decoder,
    clearTimeout(pollTimer),
    !shouldPoll())return;
    pollTimer=setTimeout(function() {
      runChallenge()}
,
    intervalState[g0(lW.l) /* "interval" */]*1e3)}
  // probabilistic gate: Math.random() < p
  // randomChance -> i
  function randomChance(l,
  lD,
  g1) {
    return lD= {
      l:453}
,
    g1=decoder,
    Math[g1(lD.l) /* "random" */]()<l}
  // true if the challenge was issued within the last hour
  // isChallengeFresh -> y
  function isChallengeFresh(lH,
  g3,
  c,
  d,
  P,
  R,
  H) {
    return lH= {
      l:437,
      c:305,
      d:331}
,
    g3=decoder,
    c= {
    }
,
    c[g3(lH.l) /* "cJGCD" */]=function(Z,
    C) {
      return Z/C}
,
    d=c,
    P=3600,
    R=challengeTimestamp(),
    H=Math[g3(lH.c) /* "floor" */](d[g3(lH.l) /* "cJGCD" */](Date[g3(lH.d) /* "now" */](),
    1e3)),
    H-R>P?![]:!![]}
  // rebuild/reload the challenge on an interval update
  // refreshChallenge -> Y
  function refreshChallenge(lB,
  fX,
  l,
  c,
  d,
  P,
  R,
  H,
  Z) {
    for(lB= {
      l:400,
      c:268,
      d:377,
      P:286,
      R:402,
      H:272,
      Z:349,
      C:448,
      O:230,
      X:385,
      f0:349,
      f1:307,
      f2:433,
      f3:241,
      f4:354,
      f5:331,
      f6:240,
      f7:307,
      f8:269,
      f9:261,
      ff:272,
      fg:214,
      fl:374,
      fc:239,
      fd:288,
      fP:269}
,
    fX=decoder,
    l= {
      "enZML":fX(lB.l) /* "7|3|9|13|10|8|11|6|4|12|5|0|2|1" */,
      "arRwm":fX(lB.c) /* "_cb" */,
      "ReRjJ":function(C,
      O) {
        return C(O)}
,
      "RVSsc":function(C) {
        return C()}
,
      "YcuVP":function(C,
      O) {
        return C(O)}
,
      "DQLGX":fX(lB.d) /* "script" */}
,
    c=l[fX(lB.P) /* "enZML" */][fX(lB.R) /* "split" */](`|`),
    d=0;
    !![];
    ) {
      switch(c[d++]) {
        case`0`:R&&(Z[fX(lB.H) /* "nonce" */]=R);
        continue;
        case`1`:P[fX(lB.Z) /* "parentNode" */][fX(lB.C) /* "replaceChild" */](Z,
        P);
        continue;
        case`2`:Z[fX(lB.O) /* "src" */]=H[fX(lB.X) /* "toString" */]();
        continue;
        case`3`:if(!P||!P[fX(lB.f0) /* "parentNode" */])return;
        continue;
        case`4`:H[fX(lB.f1) /* "searchParams" */][fX(lB.f2) /* "set" */](l[fX(lB.f3) /* "arRwm" */],
        l[fX(lB.f4) /* "ReRjJ" */](String,
        Date[fX(lB.f5) /* "now" */]()));
        continue;
        case`5`:Z[fX(lB.f6) /* "async" */]=!![];
        continue;
        case`6`:H[fX(lB.f7) /* "searchParams" */][fX(lB.f2) /* "set" */](`u`,
        String(intervalState[fX(lB.f8) /* "updates" */]));
        continue;
        case`7`:P=l[fX(lB.f9) /* "RVSsc" */](findChallengeScript);
        continue;
        case`8`:R=P[fX(lB.ff) /* "nonce" */];
        continue;
        case`9`:l[fX(lB.fg) /* "YcuVP" */](clearTimeout,
        pollTimer);
        continue;
        case`10`:globalRef[fX(lB.fl) /* "_cf_chl_state" */]=intervalState;
        continue;
        case`11`:H=new URL(P[fX(lB.O) /* "src" */]);
        continue;
        case`12`:Z=doc[fX(lB.fc) /* "createElement" */](l[fX(lB.fd) /* "DQLGX" */]);
        continue;
        case`13`:intervalState[fX(lB.fP) /* "updates" */]++;
        continue}
      break}
  }
  // prototype-chain walk: collect every own-property name up the chain (the fingerprint surface)
  // walkProtoChain -> m
  function walkProtoChain(l,
  lb,
  fn,
  c) {
    for(lb= {
      l:430,
      c:445,
      d:413}
,
    fn=decoder,
    c=[];
    null!==l;
    c=c[fn(lb.l) /* "concat" */](Object[fn(lb.c) /* "keys" */](l)),
    l=Object[fn(lb.d) /* "getPrototypeOf" */](l));
    return c}
}
();
