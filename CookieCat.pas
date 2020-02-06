{ CookieCat: a simple bitboard chess program in Pascal }

{
  The following BSD License governs the distribution and use of this program:

  Copyright (c) 2012 by the author, S. J. Edwards.
  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:

      * Redistributions of source code must retain the above copyright
        notice, this list of conditions and the following disclaimer.

      * Redistributions in binary form must reproduce the above copyright
        notice, this list of conditions and the following disclaimer in the
        documentation and/or other materials provided with the distribution.

      * Neither the name of the author nor the names of any contributors may
        be used to endorse or promote products derived from this software
        without specific prior written permission.

  This software is provided by the copyright holder and contributors "as is" and
  any express or implied warranties, including, but not limited to, the implied
  warranties of merchantability and fitness for a particular purpose are
  disclaimed.  In no event shall the copyright holder be liable for any direct,
  indirect, incidental, special, exemplary, or consequential damages (including,
  but not limited to, procurement of substitute goods or services; loss of use,
  data, or profits; or business interruption) however caused and on any theory
  of liability, whether in contract, strict liability, or tort (including
  negligence or otherwise) arising in any way out of the use of this software,
  even if advised of the possibility of such damage.
}

{
  This program was developed using the Free Pascal compiler, version 2.4.4.  For more information
  about Free Pascal, see the www.freepascal.org web site.  To download a free copy of the compiler,
  see the www.freepascal.org/download.var web page.

  The author gratefully acknowleges the work of all those who have contributed to the Free Pascal
  project.

  To install Free Pascal on Linux, try: sudo apt-get install fpc

  To compile this program for a 32 bit machine, try: fpc -O3 CookieCat.pas

  To compile this program for a 64 bit Intel/AMD machine, try: ppcx64 -O3 CookieCat.pas
}

{
  This program was developed primarily on an Apple Macintosh running the Mac OS/X 10.7 (Lion)
  operating system.  Platforms tested for both compilation and execution include:

    32 bit PowerPC   under Mac OS/X (10.4 Tiger)
    32 bit Intel/AMD under Linux    (Ubuntu 11.10)
    64 bit Intel/AMD under Windows  (Windows 7)
    64 bit Intel/AMD under Mac OS/X (10.7 Lion)
    64 bit Intel/AMD under Linux    (Ubuntu 11.10)

  Several people have contributed their time and skill helping with testing.  Their assistance
  is sincerely appreciated.

  -- Dann Corbit

  More names will appear here as permisson is granted.
}

{
  This program is an original work and not a clone; no source was copied from any other program.
  However, there are some major ideas seen here which were in use long before this program was
  written.

  The split/merge sort used in this program was discovered by John von Neumann in 1945.

  Claude Shannon wrote about the idea of a chess program in 1949.

  Alan Turing wrote the first chess program, the manually executed Turochamp, in 1950.

  The use of a bitboard representation for game pieces was first well documented by Arthur Samuel
  in the late 1950s as part of his checkers program (see: en.wikipedia.org/wiki/Arthur_Samuel).
  Samuel also wrote of many other game programming techniques used in his checker player which are
  now seen in nearly all chess playing programs.

  Alex Bernstein implemented the first machine executable chess program in 1957.

  John McCarthy, the author of the Lisp programming language, developed Lisp predicate functions
  in 1958 in part to handle chess programming conditionals.

  The use of a bitboard representation and a bitboard database for chess was developed by Larry
  Atkin and David Slate, authors of the Northwestern program Chess 4.x and also by the authors of
  the Soviet program Kaissa.  This work took place from the late 1960s to the mid 1970s.

  In 1970, Albert Zobrist developed a hashing scheme used for incremental updating of a chess
  position hash signature.

  The chess data interchange standards (EPD, FEN, PGN, and SAN) were developed by Steven Edwards
  with the help of the Usenet community and were first published in 1994.
}

{
  Other items:

  No academic, corporate, or government funding was used in the development of this program.

  All keyboarding was done using the Dvorak Simplified Keyboard layout.  For details on this
  alternative to the traditional Sholes keyboard layout, see the Wikipedia entry at the
  en.wikipedia.org/wiki/Dvorak_Simplified_Keyboard web page.

  For another Pascal bitboard chess program, see Chess 0.5 from 1978 authored by Larry Atkin and
  Peter Frey.  The source is at the www.moorecad.com/standardpascal/Chess05.pas web page.
}

{ Free Pascal compilation options }

{$c-           Assertion support       Activation useful during testing }
{$h+           Implicit AnsiStrings    Activation needed for encoding long string text }
{$i-           Implicit I/O checking   Avoid activating this option }
{$inline on    Allow inline routines   May need to be set to 'off' for some targets }
{$r-           Range checking          Activation useful during testing }

{ Free Pascal compilation options for PowerPC inline bypass; this will generate some warnings }

{$ifdef cpupowerpc}
{$inline off   Disallow inline routines for PowerPC targets }
{$endif cpupowerpc}

program CookieCat;

  uses

    { Needed units }

    SysUtils,   { System utilities }

{$ifdef unix}
    cthreads,   { Thread utilities (Unix specific) }
{$endif unix}

    DateUtils;  { Date/time utilites }

  const

    { Identification }

    progname = 'CookieCat';
    progdate = '2012.10.10';
    progauth = 'S. J. Edwards';
    progyear = '2012';

    progvers = progname + ' ' + progdate;
    progcopy = progvers + '   Copyright (c) ' + progyear + ' by ' + progauth;

    { Some ASCII characters }

    asciinul = Char( 0);
    asciiht  = Char( 9);
    asciinl  = Char(10);
    asciicr  = Char(13);
    asciiesc = Char(27);
    asciisp  = Char(32);

    { Pseudorandom number generator state index length }

    prngslotmin = 0;
    prngslotmax = 30;
    prngslotlen = prngslotmax - prngslotmin + 1;

    { Hardware core limit }

    coremin = 0;
    coremax = 15;
    corelen = coremax - coremin + 1;

    { Chessboard geometry: board files }

    bfilea = 0;
    bfileb = 1;
    bfilec = 2;
    bfiled = 3;
    bfilee = 4;
    bfilef = 5;
    bfileg = 6;
    bfileh = 7;

    bfilemin = bfilea;
    bfilemax = bfileh;
    bfilelen = bfilemax - bfilemin + 1;

    { Chessboard geometry: board ranks }

    brank1 = 0;
    brank2 = 1;
    brank3 = 2;
    brank4 = 3;
    brank5 = 4;
    brank6 = 5;
    brank7 = 6;
    brank8 = 7;

    brankmin = brank1;
    brankmax = brank8;
    branklen = brankmax - brankmin + 1;

    { Chessboard geometry: flanks (east/west half board) }

    flankq = 0;
    flankk = 1;

    flankmin = flankq;
    flankmax = flankk;
    flanklen = flankmax - flankmin + 1;

    { Chessboard geometry: homesides (south/north half board) }

    homesw = 0;
    homesb = 1;

    homesmin = homesw;
    homesmax = homesb;
    homeslen = homesmax - homesmin + 1;

    { Chessboard geometry: quadrants }

    quadwq = flankq + (homesw * flanklen);
    quadwk = flankk + (homesw * flanklen);
    quadbq = flankq + (homesb * flanklen);
    quadbk = flankk + (homesb * flanklen);

    quadmin = quadwq;
    quadmax = quadbk;
    quadlen = quadmax - quadmin + 1;

    { Chessboard geometry: squares }

    sqa1 = bfilea + (brank1 * bfilelen);
    sqb1 = bfileb + (brank1 * bfilelen);
    sqc1 = bfilec + (brank1 * bfilelen);
    sqd1 = bfiled + (brank1 * bfilelen);
    sqe1 = bfilee + (brank1 * bfilelen);
    sqf1 = bfilef + (brank1 * bfilelen);
    sqg1 = bfileg + (brank1 * bfilelen);
    sqh1 = bfileh + (brank1 * bfilelen);

    sqa2 = bfilea + (brank2 * bfilelen);
    sqb2 = bfileb + (brank2 * bfilelen);
    sqc2 = bfilec + (brank2 * bfilelen);
    sqd2 = bfiled + (brank2 * bfilelen);
    sqe2 = bfilee + (brank2 * bfilelen);
    sqf2 = bfilef + (brank2 * bfilelen);
    sqg2 = bfileg + (brank2 * bfilelen);
    sqh2 = bfileh + (brank2 * bfilelen);

    sqa3 = bfilea + (brank3 * bfilelen);
    sqb3 = bfileb + (brank3 * bfilelen);
    sqc3 = bfilec + (brank3 * bfilelen);
    sqd3 = bfiled + (brank3 * bfilelen);
    sqe3 = bfilee + (brank3 * bfilelen);
    sqf3 = bfilef + (brank3 * bfilelen);
    sqg3 = bfileg + (brank3 * bfilelen);
    sqh3 = bfileh + (brank3 * bfilelen);

    sqa4 = bfilea + (brank4 * bfilelen);
    sqb4 = bfileb + (brank4 * bfilelen);
    sqc4 = bfilec + (brank4 * bfilelen);
    sqd4 = bfiled + (brank4 * bfilelen);
    sqe4 = bfilee + (brank4 * bfilelen);
    sqf4 = bfilef + (brank4 * bfilelen);
    sqg4 = bfileg + (brank4 * bfilelen);
    sqh4 = bfileh + (brank4 * bfilelen);

    sqa5 = bfilea + (brank5 * bfilelen);
    sqb5 = bfileb + (brank5 * bfilelen);
    sqc5 = bfilec + (brank5 * bfilelen);
    sqd5 = bfiled + (brank5 * bfilelen);
    sqe5 = bfilee + (brank5 * bfilelen);
    sqf5 = bfilef + (brank5 * bfilelen);
    sqg5 = bfileg + (brank5 * bfilelen);
    sqh5 = bfileh + (brank5 * bfilelen);

    sqa6 = bfilea + (brank6 * bfilelen);
    sqb6 = bfileb + (brank6 * bfilelen);
    sqc6 = bfilec + (brank6 * bfilelen);
    sqd6 = bfiled + (brank6 * bfilelen);
    sqe6 = bfilee + (brank6 * bfilelen);
    sqf6 = bfilef + (brank6 * bfilelen);
    sqg6 = bfileg + (brank6 * bfilelen);
    sqh6 = bfileh + (brank6 * bfilelen);

    sqa7 = bfilea + (brank7 * bfilelen);
    sqb7 = bfileb + (brank7 * bfilelen);
    sqc7 = bfilec + (brank7 * bfilelen);
    sqd7 = bfiled + (brank7 * bfilelen);
    sqe7 = bfilee + (brank7 * bfilelen);
    sqf7 = bfilef + (brank7 * bfilelen);
    sqg7 = bfileg + (brank7 * bfilelen);
    sqh7 = bfileh + (brank7 * bfilelen);

    sqa8 = bfilea + (brank8 * bfilelen);
    sqb8 = bfileb + (brank8 * bfilelen);
    sqc8 = bfilec + (brank8 * bfilelen);
    sqd8 = bfiled + (brank8 * bfilelen);
    sqe8 = bfilee + (brank8 * bfilelen);
    sqf8 = bfilef + (brank8 * bfilelen);
    sqg8 = bfileg + (brank8 * bfilelen);
    sqh8 = bfileh + (brank8 * bfilelen);

    sqmin = sqa1;
    sqmax = sqh8;
    sqlen = sqmax - sqmin + 1;

    sqnil = -1;

    { Chessboard geometry: directions }

    dire   =  0;
    dirn   =  1;
    dirw   =  2;
    dirs   =  3;
    dirne  =  4;
    dirnw  =  5;
    dirsw  =  6;
    dirse  =  7;
    direne =  8;
    dirnne =  9;
    dirnnw = 10;
    dirwnw = 11;
    dirwsw = 12;
    dirssw = 13;
    dirsse = 14;
    direse = 15;

    dirmin = dire;
    dirmax = direse;
    dirlen = dirmax - dirmin + 1;

    dirnil = -1;

    orthodirmin = dire;
    orthodirmax = dirs;

    diagodirmin = dirne;
    diagodirmax = dirse;

    sweepdirmin = dire;
    sweepdirmax = dirse;

    crookdirmin = direne;
    crookdirmax = direse;

    { Chessboard geometry: direction file deltas }

    dfde   =  1;
    dfdn   =  0;
    dfdw   = -1;
    dfds   =  0;
    dfdne  =  1;
    dfdnw  = -1;
    dfdsw  = -1;
    dfdse  =  1;
    dfdene =  2;
    dfdnne =  1;
    dfdnnw = -1;
    dfdwnw = -2;
    dfdwsw = -2;
    dfdssw = -1;
    dfdsse =  1;
    dfdese =  2;

    { Chessboard geometry: direction rank deltas }

    drde   =  0;
    drdn   =  1;
    drdw   =  0;
    drds   = -1;
    drdne  =  1;
    drdnw  =  1;
    drdsw  = -1;
    drdse  = -1;
    drdene =  1;
    drdnne =  2;
    drdnnw =  2;
    drdwnw =  1;
    drdwsw = -1;
    drdssw = -2;
    drdsse = -2;
    drdese = -1;

    { Chessboard geometry: direction square deltas }

    dsde   = dfde   + (drde   * bfilelen);
    dsdn   = dfdn   + (drdn   * bfilelen);
    dsdw   = dfdw   + (drdw   * bfilelen);
    dsds   = dfds   + (drds   * bfilelen);
    dsdne  = dfdne  + (drdne  * bfilelen);
    dsdnw  = dfdnw  + (drdnw  * bfilelen);
    dsdsw  = dfdsw  + (drdsw  * bfilelen);
    dsdse  = dfdse  + (drdse  * bfilelen);
    dsdene = dfdene + (drdene * bfilelen);
    dsdnne = dfdnne + (drdnne * bfilelen);
    dsdnnw = dfdnnw + (drdnnw * bfilelen);
    dsdwnw = dfdwnw + (drdwnw * bfilelen);
    dsdwsw = dfdwsw + (drdwsw * bfilelen);
    dsdssw = dfdssw + (drdssw * bfilelen);
    dsdsse = dfdsse + (drdsse * bfilelen);
    dsdese = dfdese + (drdese * bfilelen);

    { Chessboard geometry: bidirections }

    bidire  = 0;
    bidirn  = 1;
    bidirne = 2;
    bidirnw = 3;

    bidirmin = bidire;
    bidirmax = bidirnw;
    bidirlen = bidirmax - bidirmin + 1;

    { Chessmen: chessmen counts }

    ccmin = 0;
    ccmax = sqlen;

    { Chessmen: colors }

    colorw = 0;
    colorb = 1;
    colorv = 2;

    colorrmin = colorw;
    colorrmax = colorb;
    colorrlen = colorrmax - colorrmin + 1;

    colormin = colorw;
    colormax = colorv;
    colorlen = colormax - colormin + 1;

    { Chessmen: pieces }

    piecep = 0;
    piecen = 1;
    pieceb = 2;
    piecer = 3;
    pieceq = 4;
    piecek = 5;
    piecev = 6;

    piecermin = piecep;
    piecermax = piecek;
    piecerlen = piecermax - piecermin + 1;

    piecemin = piecep;
    piecemax = piecev;
    piecelen = piecemax - piecemin + 1;

    { Chessmen: men }

    manwp = piecep + (colorw * piecerlen);
    manwn = piecen + (colorw * piecerlen);
    manwb = pieceb + (colorw * piecerlen);
    manwr = piecer + (colorw * piecerlen);
    manwq = pieceq + (colorw * piecerlen);
    manwk = piecek + (colorw * piecerlen);
    manbp = piecep + (colorb * piecerlen);
    manbn = piecen + (colorb * piecerlen);
    manbb = pieceb + (colorb * piecerlen);
    manbr = piecer + (colorb * piecerlen);
    manbq = pieceq + (colorb * piecerlen);
    manbk = piecek + (colorb * piecerlen);
    manvv = manbk + 1;

    manrmin = manwp;
    manrmax = manbk;
    manrlen = manrmax - manrmin + 1;

    manmin = manwp;
    manmax = manvv;
    manlen = manmax - manmin + 1;

    { Chess move: move special case }

    mscreg = 0; { Regular move }
    mscepc = 1; { En passant capture }
    msccqs = 2; { Castles queenside }
    msccks = 3; { Castles kingside }
    mscppn = 4; { Pawn promotes to knight }
    mscppb = 5; { Pawn promotes to bishop }
    mscppr = 6; { Pawn promotes to rook }
    mscppq = 7; { Pawn promotes to queen }

    mscmin = mscreg;
    mscmax = mscppq;
    msclen = mscmax - mscmin + 1;

    { Chess move: move flags }

    mfandf =  0; { Needs algebraic notation disambiguation file letter }
    mfandr =  1; { Needs algebraic notation disambiguation rank digit }
    mfbook =  2; { Book move }
    mfcert =  3; { Certain score }
    mfchck =  4; { Checking move }
    mfchmt =  5; { Checkmating move }
    mfdraw =  6; { Drawing move }
    mfdrfm =  7; { Drawing move (fifty moves) }
    mfdrim =  8; { Drawing move (insufficient material) }
    mfdrrp =  9; { Drawing move (repetition) }
    mfdrsm = 10; { Drawing move (stalemate) }
    mfnote = 11; { Notated move (andf/andr/chck/chmt calculated) }
    mfnull = 12; { Null move }
    mfsrch = 13; { Searched }
    mftbas = 14; { Tablebase move }
    mfvoid = 15; { Void move }

    mfmin = mfandf;
    mfmax = mfvoid;
    mflen = mfmax - mfmin + 1;

    { Castling: ordinals }

    castwq = flankq + (colorw * flanklen);
    castwk = flankk + (colorw * flanklen);
    castbq = flankq + (colorb * flanklen);
    castbk = flankk + (colorb * flanklen);

    castmin = castwq;
    castmax = castbk;
    castlen = castmax - castmin + 1;

    { Scoring: pawn conversion factor }

    scorefactor = 1000000; { All scores in micropawn units }

    { Scoring: absolute bound }

    scoreabsbound = 1 shl 30;

    { Scoring: checkmates margin and distance; used for score interpretation }

    matemarginlen = 1 shl 10; { Must be greater than maximum search depth }
    matedistlen   = 1 shl 13; { Must be greater than the maximum mate length }

    { Scoring: score value constants; millipawn units }

    svbroken = 0 - scoreabsbound; { Broken score }
    svneginf = 1 - scoreabsbound; { Negative infinity score }
    svposinf = scoreabsbound - 1; { Positive infinity score }
    sveven   = 0;                 { Even score }

    { Scoring: range bounds }

    svmin = svbroken;
    svmax = svposinf;

    { Scoring: basic mate/lose scores }

    svlosein0 = svneginf + matemarginlen;     { Lose in 0 score (checkmated) }
    svmatein1 = svposinf - matemarginlen - 1; { Mate in 1 score }

    { Scoring: checkmated synonym }

    svcheckmated = svlosein0;

    { Scoring: more mate/lose scores }

    svlosein1 = svlosein0 + 1; { Lose in 1 score }
    svmatein2 = svmatein1 - 1; { Mate in 2 score }
    svlosein2 = svlosein1 + 1; { Lose in 2 score }
    svmatein3 = svmatein2 - 1; { Mate in 3 score }
    svlosein3 = svlosein2 + 1; { Lose in 3 score }
    svmatein4 = svmatein3 - 1; { Mate in 4 score }

    { Scoring: mate/lose maxima }

    svlonglose = svlosein0 + matedistlen;
    svlongmate = svmatein1 - matedistlen + 1;

    { Scoring: piece values }

    svpvpawn   = 1000000;
    svpvknight = 3200000;
    svpvbishop = 3350000;
    svpvrook   = 5000000;
    svpvqueen  = 9500000;
    svpvking   =       0;

    { Evaluation score components }

    escmobilitybishop =  0;
    escmobilityknight =  1;
    escmobilityqueen  =  2;
    escmobilityrook   =  3;
    escpawnbackward   =  4;
    escpawnconnected  =  5;
    escpawnlocation   =  6;
    escpawnisolated   =  7;
    escpawnmajority   =  8;
    escpawnmultiple   =  9;
    escpawnpassed     = 10;
    escsidetomove     = 11;

    escmin = escmobilitybishop;
    escmax = escsidetomove;
    esclen = escmax - escmin + 1;

    { Standard Algebraic Notation: maximum character length }

    sanlen = 7; { Example: Qa1xd4+ }

    { Man Placement Data: maximum character length }

    mpdlen = ((bfilelen + 1) * branklen) - 1;

    { Forsyth-Edwards Notation: maximum character length }

    fenlen = mpdlen + (1 + 1) + (1 + 4) + (1 + 2) + (1 + 3) + (1 + 4);

    { Bitboard representation }

    bbwbitmin =  0;
    bbwbitmax = 15;
    bbwbitlen = bbwbitmax - bbwbitmin + 1;

    bbwmin = 0;
    bbwmax = (sqlen div bbwbitlen) - 1;
    bbwlen = bbwmax - bbwmin + 1;

    bbwspanmin = 0;
    bbwspanmax = (1 shl bbwbitlen) - 1;
    bbwspanlen = bbwspanmax - bbwspanmin + 1;

    { Chess move generation }

    genmin =   0;
    genmax = 255;
    genlen = genmax - genmin + 1;

    { Tablebase man count }

    tbmmin = 2; { Two kings }
    tbmmax = 5; { Current limit; dependent upon tablebase type in use }

    { Tablebase slots; one slot per man }

    tbslotmin = 0;
    tbslotmax = tbmmax - 1;
    tbslotlen = tbslotmax - tbslotmin + 1;

    { Tablebase class counts, each for N men }

    tbcm02len =     1;
    tbcm03len =     6;
    tbcm04len =    36;
    tbcm05len =   146;
    tbcm06len =   511;
    tbcm07len =  1512;
    tbcm08len =  4032;
    tbcm09len =  9752;
    tbcm10len = 21942;

    tbcmin = 0;
    tbcmax = tbcm05len - 1;
    tbclen = tbcmax - tbcmin + 1;

    tbcnil = -1;

    { Tablebase class material signature indexing }

    tbcmsmin = 0;
    tbcmsmax = (tbclen * colorrlen) - 1;
    tbcmslen = tbcmsmax - tbcmsmin + 1;

    tbcmsnil = -1;

    { Tablebase open file limit }

    tbopenlimit = 24;

    { Tablebase byte score items }

    tbbsrangelen = ((256 - 4) div 2);

    tbbsunkn = -tbbsrangelen - 2; { Unknown }
    tbbsresv = -tbbsrangelen - 1; { Reserved }
    tbbslose = -tbbsrangelen - 0; { Lose In 0 (checkmated) }
    tbbsdraw =  0;                { Drawn }
    tbbsmate =  tbbsrangelen + 0; { Mate in 1 }
    tbbsbust =  tbbsrangelen + 1; { Broken }

    { Search ply range length }

    plylog = 6;            { Log2 (maximum ply + 1) }
    plylen = 1 shl plylog; { Maximum ply + 1 }
    plymin = 0;            { Minimum ply }
    plymax = plylen - 1;   { Maximum ply }

    { Search iteration length }

    iterlen = plylen div 2;
    itermin = 0;
    itermax = iterlen - 1;

    { Search terminations }

    stallbadbutone =  0; { All ply zero moves certain bad except one }
    stallcertain   =  1; { All ply zero moves have certain scores }
    stforcedlose   =  2; { Forced lose detected }
    stforcedmate   =  3; { Forced mate detected }
    stlimitdepth   =  4; { Depth limit encountered }
    stlimitnode    =  5; { Node count limit encountered }
    stlimittime    =  6; { Time limit encountered }
    stnomoves      =  7; { No moves available (checkmate/stalemate) }
    stquickdraw    =  8; { Quick draw detected }
    stquicklose    =  9; { Quick lose detected }
    stquickmate    = 10; { Quick mate detected }
    strandom       = 11; { Random pick }
    stsingleton    = 12; { Only one move }
    stsysmaxdepth  = 13; { System maximum depth reached }
    stunterminated = 14; { Search is not yet finished }

    stmin = stallbadbutone;
    stmax = stunterminated;
    stlen = stmax - stmin + 1;

    { Game terminations }

    gtcheckmate    = 0; { Checkmate }
    gtfiftymoves   = 1; { Fifty move rule draw }
    gtinsufficient = 2; { Insufficient material draw }
    gtrepetition   = 3; { Position repetition draw }
    gtstalemate    = 4; { Stalemate }
    gtunterminated = 5; { Unterminated }

    gtmin = gtcheckmate;
    gtmax = gtunterminated;
    gtlen = gtmax - gtmin + 1;

    { Game results }

    grnone = 0; { Unknown result '*' }
    grdraw = 1; { Draw           '1/2-1/2' }
    grwinw = 2; { White won      '1-0' }
    grwinb = 3; { Black won      '0-1' }
    grdfor = 4; { Double forfeit '0-0' }

    grmin = grnone;
    grmax = grdfor;
    grlen = grmax - grmin + 1;

    { PGN tag names }

    ptnevent       =  0; { Event }
    ptnsite        =  1; { Site }
    ptndate        =  2; { Date }
    ptnround       =  3; { Round }
    ptnwhite       =  4; { White }
    ptnblack       =  5; { Black }
    ptnresult      =  6; { Result }
    ptnfen         =  7; { FEN }
    ptntime        =  8; { Time }
    ptnendfen      =  9; { EndFEN }
    ptntermination = 10; { Termination }
    ptnplycount    = 11; { PlyCount }
    ptnutc         = 12; { UTC }

    ptnmin = ptnevent;
    ptnmax = ptnutc;
    ptnlen = ptnmax - ptnmin + 1;

    { Perft transposition table items }

    ttprftslog = 20;               { Log2 of entry count of the perft transposition table }
    ttprftslen = 1 shl ttprftslog; { Entry count of the perft transposition table }
    ttprftmask = ttprftslen - 1;   { Index mask for the perft transposition table }

    { Evaluation transposition table items }

    ttevalslog = 22;               { Log2 of entry count of the evaluation transposition table }
    ttevalslen = 1 shl ttevalslog; { Entry count of the evaluation transposition table }
    ttevalmask = ttevalslen - 1;   { Index mask for the evaluation transposition table }

    { Main transposition table items }

    ttmainslog = 22;               { Log2 of entry count of the main transposition table }
    ttmainslen = 1 shl ttmainslog; { Entry count of the main transposition table }
    ttmainmask = ttmainslen - 1;   { Index mask for the main transposition table }

    { Pawn transposition table items }

    ttpawnslog = 18;               { Log2 of entry count of the pawn transposition table }
    ttpawnslen = 1 shl ttpawnslog; { Entry count of the pawn transposition table }
    ttpawnmask = ttpawnslen - 1;   { Index mask for the pawn transposition table }

    { Tablebase transposition table items }

    tttbasslog = 16;               { Log2 of entry count of the tablebase transposition table }
    tttbasslen = 1 shl tttbasslog; { Entry count of the tablebase transposition table }
    tttbasmask = tttbasslen - 1;   { Index mask for the tablebase transposition table }

    { Self test perft depth bounds }

    stprdepthmin = 1;
    stprdepthmax = 3;

    { Self test perft record count }

    stprmin =  0;
    stprmax = 15;
    stprlen = stprmax - stprmin + 1;

    { Initial value constants }

    startfen = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';
    startmpd = 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR';
    startgood = colorw;
    startevil = colorb;
    startcavs = [castmin..castmax];
    startepsq = sqnil;
    starthmvc = 0;
    startfmvn = 1;

    { Options }

    optnadcc =  0; { Auto display: chess clock }
    optnadcp =  1; { Auto display: chess board }
    optnmono =  2; { Monochrome only output }
    optntrcv =  3; { Trace: current variation }
    optntrea =  4; { Trace: EPD analysis }
    optntrfd =  5; { Trace: first time node at depth }
    optntrfv =  6; { Trace: final (predicted) variation }
    optntrif =  7; { Trace: input FEN }
    optntrit =  8; { Trace: iteration start/finish }
    optntrpv =  9; { Trace: predicted variation }
    optntrst = 10; { Trace: search termination }
    optntrts = 11; { Trace: timing statistics }

    optnmin = optnadcc;
    optnmax = optntrts;
    optnlen = optnmax - optnmin + 1;

    optnnil = -1;

    { Interactive command processor commands; must be in ASCII order }

    icpcbench     =  0; { Run the benchmark }
    icpcd         =  1; { Display everything }
    icpcdao       =  2; { Display active options }
    icpcdb        =  3; { Display board }
    icpcdbbdb     =  4; { Display bitboard database }
    icpcdbcolor   =  5; { Display board (ANSI color) }
    icpcdbmono    =  6; { Display board (monochrome) }
    icpcdesc      =  7; { Display evaluation score components }
    icpcdfen      =  8; { Display FEN }
    icpcdm        =  9; { Display moves }
    icpcdmsig     = 10; { Display material signature }
    icpcdobm      = 11; { Display opening book moves }
    icpcdp        = 12; { Display position }
    icpcdpgn      = 13; { Display PGN }
    icpcdpi       = 14; { Display program identification }
    icpcdps       = 15; { Display pawn structure components }
    icpcdtbm      = 16; { Display tablebase moves }
    icpcdtbs      = 17; { Display tablebase score }
    icpcecho      = 18; { Echo parameters }
    icpcefnormal  = 19; { EPD file normalization }
    icpcexit      = 20; { Exit program }
    icpcffmate    = 21; { FEN file mate search }
    icpcffnormal  = 22; { FEN file normalization }
    icpcffperft   = 23; { FEN file perft }
    icpcg         = 24; { Search for a move and then play it }
    icpcgg        = 25; { Play both sides until the end of the game }
    icpchelp      = 26; { Show help text }
    icpcloadfen   = 27; { Load FEN from a file }
    icpcloadpgn   = 28; { Load PGN from a file }
    icpcmate      = 29; { Search for a checkmate }
    icpcmtperft   = 30; { Multithreaded ovepath enumeration to depth with full node visits }
    icpcnew       = 31; { New game }
    icpcnoop      = 32; { No operation }
    icpcoptreset  = 33; { Option(s) reset }
    icpcoptset    = 34; { Option(s) set }
    icpcperftbulk = 35; { Movepath enumeration to depth with bulk counting }
    icpcperftfull = 36; { Movepath enumeration to depth with full node visits }
    icpcperfttran = 37; { Movepath enumeration to depth with transposition table }
    icpcpfnormal  = 38; { PGN file normalization }
    icpcrg        = 39; { Generate a random game }
    icpcrgdump    = 40; { Generate a file of random games }
    icpcrgstat    = 41; { Generate random game statistics }
    icpcrm        = 42; { Retract move }
    icpcrmp       = 43; { Retract move pair}
    icpcrmts      = 44; { Retract move(s) to start }
    icpcs         = 45; { Search for a move but do not play it }
    icpcsavefen   = 46; { Save FEN to a file }
    icpcsavepgn   = 47; { Save PGN to a file }
    icpcselftest  = 48; { Run the self test }
    icpcsfen      = 49; { Set FEN }
    icpcslevfd    = 50; { Set level fixed depth }
    icpcslevfn    = 51; { Set level fixed nodes }
    icpcslevft    = 52; { Set level fixed time }
    icpcslevnt    = 53; { Set level nominal time }
    icpcslevut    = 54; { Set level unlimited time }
    icpcstag      = 55; { Set PGN tag value }
    icpctest      = 56; { Developer testing }
    icpcttreset   = 57; { Transposition table data reset }

    icpcmin = icpcbench;
    icpcmax = icpcttreset;
    icpclen = icpcmax - icpcmin + 1;

    icpcnil = -1;

  type

    { Integer ranges: unsigned }

    ui8type  = 0..255;
    ui16type = 0..65535;
    ui32type = 0..4294967295;
    ui64type = 0..18446744073709551615;

    { Integer ranges: signed }

    si8type  = -128..127;
    si16type = -32768..32767;
    si32type = -2147483648..2147483647;
    si64type = -9223372036854775808..9223372036854775807;

    { Digit ranges }

    digittype    = 0..9;
    hexdigittype = 0..15;

    { Microseconds }

    usectype = si64type; { Note: signed quanity }

    { Component time; used for intervals and limits; always non negative }

    comptimetype =
      record
        days:    0..999999;
        hours:   0..23;
        minutes: 0..59;
        seconds: 0..59;
        usecs:   0..999999
      end;

    { Timer }

    timertype =
      record
        running: Boolean;  { True if timer is running }
        countup: Boolean;  { True if timer is counting up from zero }
        current: usectype; { Zero offset value at last update }
        updated: usectype  { Epoch microseconds at last update }
      end;

    { Pseudorandom number generator internal state element count }

    prngslottype = prngslotmin..prngslotmax;

    prngtype =
      record
        svec: array [prngslottype] of ui16type { Internal state vector }
      end;

    { Hardware cores }

    coretype = coremin..coremax;

    { Relational test result }

    rtrtype = (rtrlt, rtreq, rtrgt);

    { List element counts }

    ecounttype = ui32type;

    { Tokens }

    tokenptrtype = ^tokentype; { A pointer to a token node }

    tokentype =
      record
        tstr: String;       { Token string }
        prev: tokenptrtype; { Link to previous token }
        next: tokenptrtype  { Link to next token }
      end;

    { List of tokens }

    tokenlisttype =
      record
        ecount: ecounttype;   { Element count }
        head:   tokenptrtype; { Head of token list }
        tail:   tokenptrtype  { Tail of token list }
      end;

    { Chessboard geometry: files, ranks }

    bfiletype    = bfilemin..bfilemax;
    bfilesettype = set of bfiletype;

    branktype    = brankmin..brankmax;
    branksettype = set of branktype;

    { Chessboard geometry: flanks, homesides }

    flanktype = flankmin..flankmax;
    homestype = homesmin..homesmax;

    { Chessboard geometry: quadrants }

    quadtype = quadmin..quadmax;

    { Chessboard geometry: squares }

    sqtype  = sqmin..sqmax;
    sqxtype = sqnil..sqmax;

    { Chessboard geometry: directions }

    dirtype  = dirmin..dirmax;
    dirxtype = dirnil..dirmax;

    dirsettype = set of dirtype;

    { Chessboard geometry: direction group subranges }

    orthodirtype = orthodirmin..orthodirmax;
    diagodirtype = diagodirmin..diagodirmax;
    sweepdirtype = sweepdirmin..sweepdirmax;
    crookdirtype = crookdirmin..crookdirmax;

    { Chessboard geometry: bidirection indexing }

    bidirtype = bidirmin..bidirmax;

    { Chessboard geometry: census counts }

    cctype = ccmin..ccmax;

    { Chessmen: colors }

    colorrtype = colorrmin..colorrmax;
    colortype  = colormin..colormax;

    colorsettype = set of colortype;

    { Chessmen: pieces }

    piecertype = piecermin..piecermax;
    piecetype  = piecemin..piecemax;

    piecesettype = set of piecetype;

    { Chessmen: men }

    manrtype = manrmin..manrmax;
    mantype  = manmin..manmax;

    mansettype = set of mantype;

    { One side material signature (bitfields indexed by piece) }

    osmsigtype = ui32type;

    { One side material signature color indexed vector }

    osmsigvectype = array [colorrtype] of osmsigtype;

    { Material signature (bitfields indexed by man) }

    msigtype = ui64type;

    { Score values }

    svtype = svmin..svmax;

    { Evaluation score components }

    esctype = escmin..escmax;

    { Chess move: move special case }

    msctype    = mscmin..mscmax;
    mscsettype = set of msctype;

    { Chess move: move flag range and set }

    mftype    = mfmin..mfmax;
    mfsettype = set of mftype;

    { Half move counter and full move number }

    hmvctype = ui16type;
    fmvntype = ui16type;

    { Node counts }

    nctype = ui64type;

    { Perft modes }

    perfttype = (perftbulk, perftfull, perfttran);

    { Tablebase man range }

    tbmtype = tbmmin..tbmmax;

    { Tablebase slots; one slot per man }

    tbslottype = tbslotmin..tbslotmax;

    { Tablebase slot vector }

    tbslotvectype = array [tbslottype] of sqxtype;

    { Tablebase classes }

    tbctype  = tbcmin..tbcmax;
    tbcxtype = tbcnil..tbcmax;

    { Tablebase class material signature indexing }

    tbcmstype  = tbcmsmin..tbcmsmax;
    tbcmsxtype = tbcmsnil..tbcmsmax;

    { Tablebase file seek offset }

    tbfsotype = ui32type;

    { Search ply range }

    plytype = plymin..plymax;

    { Iteration range }

    itertype = itermin..itermax;

    { Search terminations }

    sttype = stmin..stmax;

    { Chess game terminations }

    gttype = gtmin..gtmax;

    { Game results }

    grtype = grmin..grmax;

    { Chess clock }

    chessclocktype =
      record
        timervec: array [colorrtype] of timertype; { Pair of countdown timers }
        good:     colorrtype;                      { Color on the move }
        evil:     colorrtype                       { Color not on the move }
      end;

    { Chessboard census }

    censustype =
      record
        cic: array [colorrtype] of cctype; { Color indexed counts }
        mic: array [manrtype] of cctype    { Man indexed counts }
      end;

    { Chessboard }

    boardtype =
      record
        case Boolean of
          False: (sqv: array [sqtype] of mantype);              { Linear array of chessmen }
          True:  (rfv: array [branktype, bfiletype] of mantype) { Rank/file array of chessmen }
      end;

    { MPD encoded board }

    mpdtype = String[mpdlen]; { The ASCII representation of a chessboard }

    { FEN encoded position }

    fentype = String[fenlen]; { The ASCII representation of a position }

    { Move cursor }

    mctype =
      record
        fmvn: fmvntype;  { The full move number }
        good: colorrtype { The good color }
      end;

    { Chess move: a single move with a score value }

    movetype =
      record
        frsq:  sqtype;    { From square }
        tosq:  sqtype;    { To square }
        frman: mantype;   { From man }
        toman: mantype;   { To man }
        msc:   msctype;   { Special case }
        mfset: mfsettype; { Move flag set }
        sv:    svtype     { Score value }
      end;

    { SAN encoded move }

    santype = String[sanlen]; { The ASCII representation of a move }

    { Move nodes }

    mnptrtype = ^mntype; { A pointer to a move node }

    mntype =
      record
        move: movetype;  { The move }
        prev: mnptrtype; { Link to previous move node }
        next: mnptrtype  { Link to next move node }
      end;

    { List of move nodes }

    mnlisttype =
      record
        ecount: ecounttype; { Element count }
        head:   mnptrtype;  { Head of move node list }
        tail:   mnptrtype   { Tail of move node list }
      end;

    { Bitboard related ranges }

    bbwbittype  = bbwbitmin..bbwbitmax;   { Bit indexing for a bitboard word }
    bbwtype     = bbwmin..bbwmax;         { Bitboard word indexing for a bitboard }
    bbwspantype = bbwspanmin..bbwspanmax; { Indexing for a full array of bitboard words }

    { Bitboard }

    bbtype =
      record
        case Boolean of
          False: (wvec: array [bbwtype] of bbwspantype); { Array of bitboard words }
          True:  (bv64: ui64type)                        { Unsigned 64 bit value }
      end;

    { Bitboard color indexed vector }

    bbcivtype = array [colorrtype] of bbtype;

    { Bitboard man indexed vector }

    bbmivtype = array [manrtype] of bbtype;

    { Bitboard square indexed vector }

    bbsivtype = array [sqtype] of bbtype;

    { Bitboard database }

    bbdbtype =
      record
        merge: bbtype;    { All men merged }
        sweep: bbtype;    { All sweeper men }
        locbc: bbcivtype; { Locus by color }
        locbm: bbmivtype; { Locus by man }
        atkbc: bbcivtype; { Attacks by color }
        atkfs: bbsivtype; { Attacks from squares }
        atkts: bbsivtype  { Attacks to squares }
      end;

    { Hash codes }

    hashtype =
      record
        bits0: ui64type; { Unsigned 64 bit value }
        bits1: ui64type  { Unsigned 64 bit value }
      end;

    { Castling: range and set }

    casttype    = castmin..castmax;
    castsettype = set of casttype;

    { Castling: castling description record }

    cdrtype =
      record
        cmsc: msctype;     { Castling move special case }
        cach: Char;        { FEN castling availability character }
        karc: colorrtype;  { King and rook color }
        k0sq: sqtype;      { King from square }
        k1sq: sqtype;      { King to square }
        r0sq: sqtype;      { Rook from square }
        r1sq: sqtype;      { Rook to square }
        kman: mantype;     { King man }
        rman: mantype;     { Rook man }
        cabb: bbtype;      { Castling attack test bitboard }
        cvbb: bbtype;      { Castling vacant test bitboard }
        cmov: movetype     { Copy for move generation }
      end;

    { Chess move generation: indexing }

    gentype = genmin..genmax; { Range for indexing generated moves }

    { Chess move generation: generated move set }

    gmstype =
      record
        movecount: Integer;                    { Count of generated moves }
        moves:     array [gentype] of movetype { Generated moves }
      end;

    { Chess move meta generation: mode }

    mgmtype = (mgmnotated, mgmcanonical, mgmdeluxe, mgmsuperdeluxe, mgmhyperdeluxe);

    { Fold mode for tablebase pivot square }

    foldtype = (fold10, fold32);

    { Tablebase descriptor record; one per tablebase class }

    tbdrtype =
      record
        tbc:       tbctype;                      { Tablebase class }
        osmsigvec: osmsigvectype;                { One side material signature vector }
        msig:      msigtype;                     { Material signature key; not color reversed }
        mancount:  cctype;                       { Man count (total) }
        mcvec:     array [colorrtype] of cctype; { Man counts indexed by color }
        epflag:    Boolean;                      { Set if both sides have at least one pawn }
        fold:      foldtype;                     { Folding mode }
        foldslot:  tbslottype;                   { Slot to be folded }
        name:      String;                       { Class name }
        fnvec:     array [colorrtype] of String  { TB filenames indexed by color on the move }
      end;

    { Tablebase material signature mapping descriptor record; two per tablebase class }

    tbmsmtype =
      record
        tbc:   tbctype;  { Tablebase class }
        msig:  msigtype; { Material signature key; may be color reversed }
        isrev: Boolean   { Reversed sense flag }
      end;

    { EPD: value node and list }

    evnptrtype = ^evntype;

    evntype =
      record
        evstr: String;     { Value string }
        prev:  evnptrtype; { Pointer to previous value node }
        next:  evnptrtype  { Pointer to next value node }
      end;

    evnlisttype =
      record
        head: evnptrtype; { Head of EPD value list }
        tail: evnptrtype  { Tail of EPD value list }
      end;

    { EPD: operation node and list }

    eonptrtype = ^eontype;

    eontype =
      record
        eostr:   String;      { Opcode string }
        evnlist: evnlisttype; { EPD value node list }
        prev:    eonptrtype;  { Pointer to previous operation node }
        next:    eonptrtype   { Pointer to next operation node }
      end;

    eonlisttype =
      record
        head: eonptrtype; { Head of EPD operation list }
        tail: eonptrtype  { Tail of EPD operation list }
      end;

    { EPD: entire record }

    epdtype =
      record
        fen:     fentype;    { Position FEN }
        eonlist: eonlisttype { EPD operation list }
      end;

    { Pawn structure }

    pawnstructtype =
      record
        backward:  bbcivtype; { Backward pawns by color }
        connected: bbcivtype; { Connected pawns by color }
        isolated:  bbcivtype; { Isolated pawns by color }
        location:  bbcivtype; { Locus of pawns by color }
        majority:  bbcivtype; { Three file majority pawns by color }
        multiple:  bbcivtype; { Doubled (and worse) multiple pawns by color }
        passed:    bbcivtype  { Passed pawns by color }
      end;

    { Perft transposition table items }

    ttprftsigtype =
      record
        sigword0: ui64type; { From hash bits 0 and draft (in bottom byte) }
        sigword1: ui64type  { From hash bits 1 }
      end;

    ttprftentrytype =
      record
        ttprftsig: ttprftsigtype; { Perft signature from hash and draft }
        pathcount: nctype         { Path count }
      end;

    ttprftindextype = 0..ttprftmask;                               { Perft TT storage index }
    ttprftptrtype   = ^ttprfttype;                                 { Pointer to perft TT storage }
    ttprfttype      = array [ttprftindextype] of ttprftentrytype;  { Perft TT storage }

    { Evaluation transposition table entry: flag data }

    { Bits 0 - 0: 0/Free, 1/In use }
    { Bits 1 - 1: 0/WTM, 1/BTM }
    { Bits 7 - 2: Unused }

    { Evaluation transposition table items }

    ttevalentrytype =
      record
        hash:     hashtype; { Entry signature (from position mphc hash) }
        score:    svtype;   { Associated score }
        flagdata: ui8type   { Packed flag data }
      end;

    ttevalindextype = 0..ttevalmask;                               { Evaluation TT storage index }
    ttevalptrtype   = ^ttevaltype;                                 { Pointer to evaluation TT storage }
    ttevaltype      = array [ttevalindextype] of ttevalentrytype;  { Evaluation TT storage }

    { Main transposition table score interpretation mode }

    tsimtype =
      (
        tsimnone,  { Score is missing }
        tsimexact, { Score is exact }
        tsimlower, { Score is a lower bound }
        tsimupper  { Score is an upper bound }
      );

    { Main transposition table entry: flag data }

    { Bits 0 - 0: 0/Free, 1/In use }
    { Bits 1 - 1: 0/WTM, 1/BTM }
    { Bits 3 - 2: tsim }
    { Bits 7 - 4: Unused }

    { Main transposition table entry: move data }

    { Bits  5 -  0: From square }
    { Bits 11 -  6: To square }
    { Bits 14 - 12: msc }
    { Bits 15 - 15: Unused }

    { Main transposition table items }

    ttmainentrytype =
      record
        hash:     hashtype; { Entry signature (from position mphc hash) }
        score:    svtype;   { Associated score or bound, if any }
        draft:    si8type;  { Draft of analysis }
        flagdata: ui8type;  { Packed flag data }
        movedata: ui16type  { Packed from-square, to-square, msc }
      end;

    ttmainindextype = 0..ttmainmask;                               { Main TT storage index }
    ttmainptrtype   = ^ttmaintype;                                 { Pointer to main TT storage }
    ttmaintype      = array [ttmainindextype] of ttmainentrytype;  { Main TT storage }

    { Pawn transposition table entry: flag data }

    { Bits 0 - 0: 0/Free, 1/In use }
    { Bits 1 - 1: 0/WTM, 1/BTM }
    { Bits 7 - 2: Unused }

    { Pawn transposition table items }

    ttpawnentrytype =
      record
        hash:       hashtype;       { Entry signature (from position pshc hash) }
        pawnstruct: pawnstructtype; { Pawn structure }
        score:      svtype;         { Associated score }
        flagdata:   ui8type         { Packed flag data }
      end;

    ttpawnindextype = 0..ttpawnmask;                               { Pawn TT storage index }
    ttpawnptrtype   = ^ttpawntype;                                 { Pointer to pawn TT storage }
    ttpawntype      = array [ttpawnindextype] of ttpawnentrytype;  { Pawn TT storage }

    { Tablebase transposition table entry: flag data }

    { Bits 0 - 0: 0/Free, 1/In use }
    { Bits 1 - 1: 0/WTM, 1/BTM }
    { Bits 7 - 2: Unused }

    { Tablebase transposition table items }

    tttbasentrytype =
      record
        hash:     hashtype; { Entry signature (from position mphc hash) }
        score:    svtype;   { Associated score }
        flagdata: ui8type   { Packed flag data }
      end;

    tttbasindextype = 0..tttbasmask;                               { Tablebase TT storage index }
    tttbasptrtype   = ^tttbastype;                                 { Pointer to tablebase TT storage }
    tttbastype      = array [tttbasindextype] of tttbasentrytype;  { Tablebase TT storage }

    { Self test perft record }

    stprdepthtype = stprdepthmin..stprdepthmax;

    stprtype = stprmin..stprmax;

    stpdtype =
      record
        fen:  fentype;                        { Test position FEN }
        tvec: array [stprdepthtype] of nctype { Target perft counts for depths 1 through N }
      end;

    { Check detection runway }

    runwaytype =
      record
        prwbb: bbtype; { Landing runway for pawn attackers }
        nrwbb: bbtype; { Landing runway for knight attackers }
        brwbb: bbtype; { Landing runway for bishop attackers }
        rrwbb: bbtype; { Landing runway for rook attackers }
        qrwbb: bbtype; { Landing runway for queen attackers }
        disbb: bbtype  { Discovery candidates }
      end;

    { Variation }

    variationtype =
      record
        freelist: mnlisttype; { Free move nodes }
        usedlist: mnlisttype  { Move nodes in played order }
      end;

    { Alpha/beta window }

    windowtype =
      record
        alfa: svtype; { Lower bound score value }
        beta: svtype  { Upper bound score value }
      end;

    { PGN tag names }

    ptntype = ptnmin..ptnmax;

    ptpairtype =
      record
        ptn: ptntype; { Tag name index }
        use: Boolean; { In use flag }
        tag: String   { Tag string value }
      end;

    { PGN game }

    pgngametype =
      record
        ptnvec: array [ptntype] of ptpairtype; { Tag pairs }
        ifen:   fentype;                       { Initial FEN }
        imc:    mctype;                        { Initial move cursor }
        gr:     grtype;                        { Game result }
        mnlist: mnlisttype                     { Moves }
      end;

    { Spev: Saved position environmental values }

    spevptrtype = ^spevtype; { Pointer to a spev }

    spevtype =
      record
        spevmove: movetype;    { Move to be played }
        spevgood: colorrtype;  { Color on the move }
        spevevil: colorrtype;  { Color not on the move }
        spevcavs: castsettype; { Castling availability value set }
        spevepsq: sqxtype;     { En passant target square }
        spevhmvc: hmvctype;    { Half move counter }
        spevfmvn: fmvntype;    { Full move number }
        spevinch: Boolean;     { In check flag }
        spevdbch: Boolean;     { Double check flag }
        spevpmbb: bbtype;      { Pinned man bitboard }
        spevfmbb: bbtype;      { Frozen man bitboard }
        spevmphc: hashtype;    { Main position hash code (saved but not restored) }
        prev:     spevptrtype; { Link to previous spev node }
        next:     spevptrtype  { Link to next spev node }
      end;

    { List of saved position environmental values }

    spevlisttype =
      record
        ecount: ecounttype;  { Element count }
        head:   spevptrtype; { Head of spev list }
        tail:   spevptrtype  { Tail of spev list }
      end;

    { Chess position }

    postype =
      record
        board:        boardtype;                     { Chessboard }
        good:         colorrtype;                    { Color on the move }
        evil:         colorrtype;                    { Color not on the move }
        cavs:         castsettype;                   { Castling availability value set }
        epsq:         sqxtype;                       { En passant target square }
        hmvc:         hmvctype;                      { Half move counter }
        fmvn:         fmvntype;                      { Full move number }
        bbdb:         bbdbtype;                      { Bitboard database }
        msig:         msigtype;                      { Material signature }
        wood:         cctype;                        { Man count }
        census:       censustype;                    { Material census }
        matv:         array [colorrtype] of svtype;  { Material score values }
        ksqv:         array [colorrtype] of sqxtype; { King locations }
        inch:         Boolean;                       { In check flag }
        dbch:         Boolean;                       { Double check flag }
        pmbb:         bbtype;                        { Pinned man bitboard }
        fmbb:         bbtype;                        { Frozen man bitboard }
        mphc:         hashtype;                      { Main position hash code }
        pshc:         hashtype;                      { Pawn structure hash code }
        ifen:         fentype;                       { Initial FEN string }
        freespevlist: spevlisttype;                  { Free spev list }
        usedspevlist: spevlisttype                   { Used spev list }
      end;

    { Perft block parameter record }

    perftblocktype =
      record
        threadid:  TThreadID; { Thread ID }
        ifen:      fentype;   { Position FEN }
        draft:     Integer;   { Draft of calculation }
        prior:     santype;   { Prior move SAN }
        mpcount:   nctype;    { Result movepath count }
        completed: Boolean    { Completion flag }
      end;

    perftblockptrtype = ^perftblocktype;

    { Game termination statistics summation vector }

    gtstatstype = array [gttype] of nctype; { Vector of game termination counts }

    { Options indexing }

    optntype  = optnmin..optnmax;
    optnxtype = optnnil..optnmax;

    { Options set }

    optnsettype = set of optntype;

    { Killers }

    killerstype =
      record
        k0move: movetype; { Most recent killer move }
        k1move: movetype  { Second most recent killer move }
      end;

    { Pick move state }

    pmstype =
      (
        pmsstart,      { Start the pick process for this ply }
        pmscyclenext,  { Try first unsearched move (repeated until exhaustion) }
        pmscyclebest,  { Try best unsearched move (repeated until exhaustion) }
        pmsordering,   { Calculate and assign move ordering scores }
        pmspredvar,    { Try predicted variation move }
        pmstranstable  { Try transposition table move }
      );

    { Node search state }

    nsstype =
      (
        nssplystart,    { Ply start }
        nssplyfinish,   { Ply finish }
        nssfirdrawtest, { FIR draw test }
        nsstbprobe,     { Tablebase probe }
        nsstermtest,    { Mate finder terminal node test }
        nssstandtest,   { Quiescence stand pat test }
        nssgenerate,    { Move generation }
        nssmovepick,    { Move selection }
        nssexecute,     { Move execute }
        nssretract,     { Move retract }
        nsspostscan,    { Scan complete }
        nssexit         { Exit from search }
      );

    { Ply indexed record }

    pirtype =
      record
        isplyzero:     Boolean;       { Constant ply zero flag; set only for the ply zero }
        isplyone:      Boolean;       { Constant ply one flag; set only for the ply one }
        islastply:     Boolean;       { Constant last ply flag; set only for the last ply }
        isdrawtest:    Boolean;       { Constant draw test flag; set only for ply > 1 }
        ispzmover:     Boolean;       { Constant ply zero mover flag; set only for even ply }
        isgainersonly: Boolean;       { Gainer move generation flag }
        standsv:       svtype;        { Non gain static score }
        nss:           nsstype;       { Node search state }
        pms:           pmstype;       { Move pick state }
        window:        windowtype;    { Input window; score result returned via alfa value }
        depth:         Integer;       { Input depth value }
        extension:     Integer;       { Depth extension }
        pv:            variationtype; { Predicted variation result }
        pickcount:     Integer;       { Number of moves picked }
        killers:       killerstype;   { Killer move data }
        bestmove:      movetype;      { Best move }
        srchmove:      movetype;      { Move currently searched }
        srchsv:        svtype;        { Returned score for the searched move }
        gms:           gmstype        { Moves }
      end;

    { Vector of ply indexed records }

    pirvectype = array [plytype] of pirtype;

    { Iteration indexed record }

    iirtype =
      record
        sv: svtype { Score for the iteration }
      end;

    { Vector of iteration indexed records }

    iirvectype = array [itertype] of iirtype;

    { Search resource limit flavor }

    srlftype = (srlfiter, srlfnode, srlfftim, srlfmtim, srlfnone);

    { Search resource limit }

    srltype =
      record
        case srlf: srlftype of
          srlfiter: (limititer: Integer);  { Iteration limit }
          srlfnode: (limitnode: nctype);   { Node count limit }
          srlfftim: (limitftim: usectype); { Fixed microsecond limit }
          srlfmtim: (limitmtim: usectype); { Mean microsecond limit }
          srlfnone: ()                     { No limit }
      end;

    { Tablebase byte score }

    tbbstype = tbbsunkn..tbbsbust;

    { Tablebase file }

    tbftype    = file of tbbstype;
    tbfptrtype = ^tbftype;

    { Tablebase file record }

    tbfrtype =
      record
        broken: Boolean;    { True if open, seek, or read failed }
        name:   String;     { File name }
        tbfptr: tbfptrtype  { Pointer to file }
      end;

    { Tablebase file record vector }

    tbfrvectype    = array [tbcmstype] of tbfrtype;
    tbfrvecptrtype = ^tbfrvectype;

    { Tablebase wrangler }

    tbwranglertype =
      record
        opencount:  ui32type;       { Count of open files }
        replindex:  ui32type;       { Replacement candidate index }
        tbfrvecptr: tbfrvecptrtype; { Pointer to tablebase file record vector }
        tttbasptr:  tttbasptrtype   { Pointer to tablebase transposititon table }
      end;

    { Selection/search context }

    ssctype =
      record
        ssctimer:   timertype;      { Selection/search context timer }
        sscoptnset: optnsettype;    { Snapshot of command processing context option vector }
        tracefile:  Text;           { Output only trace file }
        rootpos:    postype;        { Root position }
        rootgms:    gmstype;        { Root moves }
        rootwindow: windowtype;     { Root A/B window }
        isleftmost: Boolean;        { Set only for leftmost branch }
        currpos:    postype;        { Current position }
        currvar:    variationtype;  { Current variation }
        srl:        srltype;        { Search resource limit }
        priorpv:    variationtype;  { Predicted variation from the prior iteration }
        predsv:     svtype;         { Result: predicted score }
        predvar:    variationtype;  { Result: predicted variation }
        nodecount:  nctype;         { Result: number of nodes searched }
        usedusec:   usectype;       { Result: microseconds used }
        st:         sttype;         { Result: search termination }
        ttevalptr:  ttevalptrtype;  { Pointer to evaluation transposititon table }
        ttmainptr:  ttmainptrtype;  { Pointer to main transposititon table }
        ttpawnptr:  ttpawnptrtype;  { Pointer to pawn transposititon table }
        tbwrangler: tbwranglertype; { Tablebase wrangler }
        pirvec:     pirvectype;     { Ply indexed record vector }
        iirvec:     iirvectype      { Iteration indexed record vector }
      end;

    sscptrtype = ^ssctype;

    { Array of pointers to selection/search contexts }

    sscptrvectype = array [coretype] of sscptrtype;

    { Command processing context }

    cpctype =
      record
        cpctimer:   timertype;     { Command processing context elapsed time timer }
        cpcoptnset: optnsettype;   { Option vector; copy to ssc on search dispatch }
        prng:       prngtype;      { Pseudorandom number generator }
        ifile:      Text;          { Default text input file }
        ofile:      Text;          { Default text output file }
        efile:      Text;          { Default text error file }
        exiting:    Boolean;       { Pending exit flag }
        ctlist:     tokenlisttype; { The command token list }
        cpcpos:     postype;       { The position }
        pgngame:    pgngametype;   { The PGN game }
        sscptrvec:  sscptrvectype  { Pointers to selection/search contexts }
      end;

    { Interactive command processor commands }

    icpctype  = icpcmin..icpcmax;
    icpcxtype = icpcnil..icpcmax;

    { Command processor: Interactive }

    icptype =
      record
        cpc:  cpctype;  { The command proccessing context for this command processor }
        icpc: icpcxtype { Command to be processed }
      end;

    { Command processor: SCI } {TBD}

    scptype =
      record
        cpc: cpctype { The command proccessing context for this command processor }
      end;

  var

    { Constant prime numbers for pseudorandom number generation }

    primes1vec, primes2vec: array [prngslottype] of ui16type;

    { Constant chessboard file indexed items }

    bfiletochar: array [bfiletype] of Char;      { File ASCII characters }
    otherbfile:  array [bfiletype] of bfiletype; { Other file }

    { Constant chessboard rank indexed items }

    branktochar:  array [branktype] of Char;                  { Rank ASCII characters }
    otherbrank:   array [branktype] of branktype;             { Other rank }
    normalbrank:  array [colorrtype, branktype] of branktype; { Ranks normalized by color }
    epranktogood: array [branktype] of colortype;             { En passant target rank to good }

    { Constant chessboard square indexed items }

    sqtobfile: array [sqtype] of bfiletype;  { Square file }
    sqtobrank: array [sqtype] of branktype;  { Square rank }
    sqtocolor: array [sqtype] of colorrtype; { Square color }

    bfilebranktosq: array [bfiletype, branktype] of sqtype; { File+rank to square }

    reflectx0: array [sqtype] of sqtype; { Reflect squares along x=0 }
    reflecty0: array [sqtype] of sqtype; { Reflect squares along y=0 }
    reflectxy: array [sqtype] of sqtype; { Reflect squares along x=y }

    { Constant direction indexed items }

    dirtobfiledelta: array [dirtype] of si8type; { File deltas }
    dirtobrankdelta: array [dirtype] of si8type; { Rank deltas }
    dirtosqdelta:    array [dirtype] of si8type; { Square deltas }

    otherdir: array [dirtype] of dirtype; { Other direction }

    dirtobidir: array [sweepdirtype] of bidirtype; { Map sweep direction to bidirection }

    orthodirset, diagodirset, sweepdirset, crookdirset: dirsettype; { Direction selection sets }

    { Constant color indexed items }

    colornames:  array [colorrtype] of String; { Color names }
    playernames: array [colorrtype] of String; { Player names }
    colortochar: array [colorrtype] of Char;   { Color ASCII characters }

    othercolor:  array [colorrtype] of colortype; { Other color }

    pawnadvdir: array [colorrtype] of dirtype; { Pawn advance directions by color }
    pawnretdir: array [colorrtype] of dirtype; { Pawn retreat directions by color }

    colortocavs:      array [colorrtype] of castsettype; { Castling avaliability masks by color }
    colortocastling0: array [colorrtype] of casttype;    { First castling by color }
    colortocastling1: array [colorrtype] of casttype;    { Final castling by color }

    synthpawn:   array [colorrtype] of manrtype; { Synthesize a pawn by color }
    synthknight: array [colorrtype] of manrtype; { Synthesize a knight by color }
    synthbishop: array [colorrtype] of manrtype; { Synthesize a bishop by color }
    synthrook:   array [colorrtype] of manrtype; { Synthesize a rook by color }
    synthqueen:  array [colorrtype] of manrtype; { Synthesize a queen by color }
    synthking:   array [colorrtype] of manrtype; { Synthesize a king by color }

    { Constant piece indexed items }

    piecenames:  array [piecertype] of String; { Piece names }
    piecetochar: array [piecertype] of Char;   { Piece ASCII characters }

    piecetosv:   array [piecetype] of svtype; { Piece score values }

    osmsigdeltavec: array [piecertype] of osmsigtype; { Map piece to one side material signature delta }

    { Constant color/piece indexed items }

    colorpiecetoman: array [colorrtype, piecertype] of manrtype; { Map color and piece to man }

    { Constant man indexed items }

    mannames:  array [manrtype] of String; { Man names }
    mantochar: array [manrtype] of Char;   { Man ASCII characters }

    mantocolor: array [mantype] of colortype;  { Map man to color }
    mantopiece: array [mantype] of piecetype;  { Map man to piece }

    otherman: array [mantype] of mantype; { Other man from piece and other color }

    mantosv: array [mantype] of svtype;     { Man score values }

    mantodir0: array [manrtype] of dirtype; { Map man to first attack direction }
    mantodir1: array [manrtype] of dirtype; { Map man to final attack direction }

    msigdeltavec: array [manrtype] of msigtype; { Map man to material signature delta }

    pawnmanset: mansettype; { Pawns }
    kingmanset: mansettype; { Kings }

    sweepermanset: mansettype; { Bishops, rooks, and queens }

    manatk0setvec: array [colorrtype, sweepdirtype] of mansettype; { Incoming attackers (start) }
    manatk1setvec: array [colorrtype, sweepdirtype] of mansettype; { Incoming attackers (further) }

    { Constant move special case indexed items }

    msctopiece: array [msctype] of piecetype; { Map msc to piece }
    msctogain:  array [msctype] of svtype;    { Map msc to additional gain score }

    gainmscset: mscsettype; { Special gainers }
    prommscset: mscsettype; { Promotions }

    { Constant move flag indexed items }

    mfnames: array [mftype] of String; { Move flag names }

    { Constant evaluation score component indexed items }

    escnames: array [esctype] of String; { Evaluation score components: names }
    escsvvec: array [esctype] of svtype; { Evaluation score components: values }

    { Constant tablebase items }

    tbdrvec:  array [tbctype] of tbdrtype;    { TB descriptors; ordered by class name }
    tbmsmvec: array [tbcmstype] of tbmsmtype; { TB lookup table; ordered by signature }

    fold10map: array [sqtype] of Integer; { Map square to folding mode 10 offset }
    fold32map: array [sqtype] of Integer; { Map square to folding mode 32 offset }

    { Constant search termination indexed items }

    stnames: array [sttype] of String; { Search termination names }

    { Constant game termination indexed items }

    gtnames: array [gttype] of String; { Game termination names }

    colorgttogr: array [colorrtype, gttype] of grtype; { Map good color and gt to result }

    { Constant game result indexed items }

    grnames: array [grtype] of String; { Game result names }

    { Constant PGN tag name indexed items }

    ptnnames: array [ptntype] of String; { PGN tag names }

    { Constant directional tables }

    advance: array [sqtype, dirtype] of sqxtype; { Next square along any direction }
    onboard: array [sqtype, dirtype] of Boolean; { True if next square is on the board }
    compass: array [sqtype, sqtype] of dirxtype; { Direction from first to second square }
    shadows: array [sqtype, sqtype] of sqxtype;  { First square beyond a line segment }

    { Constant square scanning tables }

    scansqs: array [0..511] of sqxtype;                { Sequences of scan squares; magic upper bound }
    scanmap: array [sqtype, sweepdirtype] of si16type; { Map to starting index in scan square table }

    { Constant bitboard word indexed tables }

    bitcountvec: array [bbwspantype] of 0..bbwbitlen;  { Count of active bits in a bitboard word }
    bitfirstvec: array [bbwspantype] of -1..bbwbitmax; { First active bit in a bitboard word }

    { Constant bitboards }

    bermudabb: bbtype; { Bermuda triangle used for tablebase square flip detection }

    { Constant bitboard vectors and arrays }

    singlebitbbvec: bbsivtype; { A single bit for a square }
    cancelbitbbvec: bbsivtype; { The complement of a single bit for a square }

    doublebitbbvec: array [sqtype, sqtype] of bbtype; { Two bits for two squares }

    bfilebbvec: array [bfiletype] of bbtype; { Squares on a file }
    brankbbvec: array [branktype] of bbtype; { Squares on a rank }

    flankbbvec: array [flanktype] of bbtype; { Squares on a flank }
    homesbbvec: array [homestype] of bbtype; { Squares on a home side }

    quadbbvec: array [quadtype] of bbtype; { Squares on a quadrant }

    edgebbvec: array [sweepdirtype] of bbtype; { Edges along a sweep direction }

    pawnatkbbvec:   array [colorrtype, sqtype] of bbtype; { Pawn attack squares }
    knightatkbbvec: bbsivtype;                            { Knight attack squares }
    kingatkbbvec:   bbsivtype;                            { King attack squares }

    openraybbvec: array [sqtype, sweepdirtype] of bbtype; { Open ray squares }
    pathwaybbvec: array [sqtype, sqtype] of bbtype;       { Pathway squares }

    beambbvec: array [sqtype, sqtype] of bbtype; { Beam squares from first through second square }

    orthoraybbvec: bbsivtype; { Orthogonal rays from a square }
    diagoraybbvec: bbsivtype; { Diagonal rays from a square }
    sweepraybbvec: bbsivtype; { Sweep rays from a square }

    lateralbbvec: bbsivtype; { East/west adjacent squares of a square }
    adjfilebbvec: bbsivtype; { East/west adjacent file squares of a square }
    connectbbvec: bbsivtype; { Connected adjacent file squares of a square }
    majfilebbvec: bbsivtype; { Two/three file majority file squares of a square }

    guardedbbvec: array [colorrtype, sqtype] of bbtype; { Actual/potental pawn guard masks }

    ptrackbbvec: array [colorrtype, sqtype] of bbtype; { Pawn forward track }
    passerbbvec: array [colorrtype, sqtype] of bbtype; { Passed pawn forward test squares }

    { Constant attack counts }

    pawnatkccvec:   array [colorrtype, sqtype] of cctype; { Pawn attack square counts }
    knightatkccvec: array [sqtype] of cctype;             { Knight attack square counts }
    kingatkccvec:   array [sqtype] of cctype;             { King attack square counts }

    { Constant hashes }

    hashmansqvec:    array [manrtype, sqtype] of hashtype; { Man/square hash codes }
    hashcastlingvec: array [casttype] of hashtype;         { Castling availability hash codes }
    hashepfilevec:   array [bfiletype] of hashtype;        { En passant file hash codes }

    { Constant castling descriptor records }

    cdrvec: array [casttype] of cdrtype; { Castling descriptor records }

    { Constant self test perft records }

    stprvec: array [stprtype] of stpdtype; { Data for self test perft calculations }

    { Constant moves }

    nullmove: movetype; { The prototype null move }
    voidmove: movetype; { The prototype void move }

    { Constant pawn advancement tables }

    pawnloc0: array [colorrtype, sqtype] of Integer; { Pawn advancement 0 merit vector }
    pawnloc1: array [colorrtype, sqtype] of Integer; { Pawn advancement 1 merit vector }

    { Constant initial value chessboard }

    startboard: boardtype; { The initial array chessboard }

    { Constant option items }

    optnnames: array [optntype] of String; { Option names }
    optnhelps: array [optntype] of String; { Option help strings }

    { Constant interactive command processor items }

    icpcnames: array [icpctype] of String; { Command verbs for an ICP }
    icpchelps: array [icpctype] of String; { Command help strings for an ICP }

  procedure AvoidSomeCompilerWarnings;
  begin
    Assert(dirtobidir[0] = dirtobidir[0]);
    Assert(sweepdirset = sweepdirset);
    Assert(crookdirset = crookdirset);
    Assert(prommscset = prommscset);
    Assert(pawnatkccvec[0, 0] = pawnatkccvec[0, 0]);
    Assert(kingatkccvec[0] = kingatkccvec[0])
  end; { AvoidSomeCompilerWarnings }

  { ***** System routines ***** }

  procedure WTF(str: String);
  begin
    WriteLn(StdErr, 'Internal error: ', str);
    Halt
  end; { WTF }

  function EpochUsec: usectype;
    var
      timestamp: TTimeStamp;
  begin
    timestamp := DateTimeToTimeStamp(Now);
    EpochUsec := ((si64type(timestamp.date) * 86400000) + timestamp.time) * 1000
  end; { EpochUsec }

  procedure RatNap;
  begin
    Sleep(10)
  end; { RatNap }

  procedure CatNap;
  begin
    Sleep(100)
  end; { CatNap }

  procedure DogNap;
  begin
    Sleep(1000)
  end; { DogNap }

  function CalcCoreCount: Integer;
    var
      myresult: Integer;
  begin
    myresult := 4; {TBD}
    if myresult > corelen then
      myresult := corelen;
    CalcCoreCount := myresult
  end; { CalcCoreCount }

  { ***** Simple output routines ***** }

  procedure WriteCh(var ofile: Text; ch: Char);
  begin
    Write(ofile, ch)
  end; { WriteCh }

  procedure WriteNL(var ofile: Text);
  begin
    WriteCh(ofile, asciinl)
  end; { WriteNL }

  procedure WriteStr(var ofile: Text; str: String);
    var
      index, limit: Integer;
  begin
    limit := Length(str);
    for index := 0 to limit - 1 do
      WriteCh(ofile, str[index + 1])
  end; { WriteStr }

  procedure WriteStrNL(var ofile: Text; str: String);
  begin
    WriteStr(ofile, str);
    WriteNL(ofile)
  end; { WriteStrNL }

  procedure WriteIndent(var ofile: Text; level: Integer);
    var
      index: Integer;
  begin
    for index := 0 to level - 1 do
      WriteCh(ofile, asciisp)
  end; { WriteIndent }

  procedure WritePrefix(var ofile: Text; str: String);
  begin
    WriteStr(ofile, '[' + str + '] ');
  end; { WritePrefix }

  { ***** Component Time routines ***** }

  procedure CompTimeLoadFromUsec(var comptime: comptimetype; usec: usectype);
    var
      residue: usectype;
  begin
    Assert((usec >= 0), 'CompTimeLoadFromUsec: usec fault');
    with comptime do
      begin
        residue := usec;
        usecs   := residue mod 1000000;
        residue := residue div 1000000;
        seconds := residue mod 60;
        residue := residue div 60;
        minutes := residue mod 60;
        residue := residue div 60;
        hours   := residue mod 24;
        residue := residue div 24;
        days    := residue mod 1000000
      end
  end; { CompTimeLoadFromUsec }

  function CompTimeEncode(var comptime: comptimetype): String;
  begin
    with comptime do
      CompTimeEncode :=
          Format('%.3d.%.2d:%.2d:%.2d.%.3d', [days, hours, minutes, seconds, (usecs div 1000)])
  end; { CompTimeEncode }

  { ***** Timer routines ***** }

  procedure TimerReset(var timer: timertype);
  begin
    with timer do
      begin
        running := False;
        countup := True;
        current := 0;
        updated := EpochUsec
      end
  end; { TimerReset }

  procedure TimerUpdate(var timer: timertype);
    var
      updateusec, deltausec: usectype;
  begin
    with timer do
      begin
        updateusec := EpochUsec;
        deltausec := updateusec - updated;
        updated := updateusec;
        if running then
          if countup then
            Inc(current, deltausec)
          else
            if current < deltausec then
              current := 0
            else
              Dec(current, deltausec)
      end
  end; { TimerUpdate }

  procedure TimerStart(var timer: timertype);
  begin
    with timer do
      begin
        TimerUpdate(timer);
        if not running then
          running := True
      end
  end; { TimerStart }

  procedure TimerStop(var timer: timertype);
  begin
    with timer do
      begin
        TimerUpdate(timer);
        if running then
          running := False
      end
  end; { TimerStop }

  procedure TimerResetThenStart(var timer: timertype);
  begin
    TimerReset(timer);
    TimerStart(timer)
  end; { TimerResetThenStart }

  function TimerCurrent(var timer: timertype): usectype;
  begin
    with timer do
      begin
        TimerUpdate(timer);
        TimerCurrent := current
      end
  end; { TimerCurrent }

  function TimerEncode(var timer: timertype): String;
    var
      comptime: comptimetype;
  begin
    CompTimeLoadFromUsec(comptime, TimerCurrent(timer));
    TimerEncode := CompTimeEncode(comptime)
  end; { TimerEncode }

  { ***** Pseudorandom number generator routines ***** }

  procedure PrngReset(var prng: prngtype);
    var
      prngslot: prngslottype;
  begin
    with prng do
      for prngslot := prngslotmin to prngslotmax do
        svec[prngslot] := 0
  end; { PrngReset }

  procedure PrngRandomize(var prng: prngtype);
    var
      prngslot: prngslottype;
  begin
    with prng do
      for prngslot := prngslotmin to prngslotmax do
        svec[prngslot] := Random(primes2vec[prngslot])
  end; { PrngRandomize }

  procedure PrngAdvance(var prng: prngtype);
    var
      prngslot: prngslottype;
  begin
    with prng do
      for prngslot := prngslotmin to prngslotmax do
        begin
          Inc(svec[prngslot]);
          if svec[prngslot] = primes2vec[prngslot] then
            svec[prngslot] := 0
        end
  end; { PrngAdvance }

  function PrngHasOddParity(var prng: prngtype): Boolean;
    var
      myresult: Boolean;
      prngslot: prngslottype;
  begin
    with prng do
      begin
        myresult := False;
        for prngslot := prngslotmin to prngslotmax do
          if svec[prngslot] >= primes1vec[prngslot] then
            myresult := not myresult
      end;
    PrngHasOddParity := myresult
  end; { PrngHasOddParity }

  function PrngNextBit(var prng: prngtype): Integer;
    var
      myresult: Integer;
  begin
    if PrngHasOddParity(prng) then
      myresult := 1
    else
      myresult := 0;
    PrngAdvance(prng);
    PrngNextBit := myresult
  end; { PrngNextBit }

  function PrngRandom(var prng: prngtype; bound: Integer): Integer;
    var
      bitindex: Integer;
      dividend: ui32type;
  begin
    Assert((bound > 0), 'PrngRandom: bound fault');
    dividend := 0;
    for bitindex := 0 to 30 do
      begin
        dividend := dividend shl 1;
        if PrngNextBit(prng) <> 0 then
          Inc(dividend)
        end;
    PrngRandom := dividend mod bound
  end; { PrngRandom }

  { ***** Character/string predicates ***** }

  function IsCharWhiteSpace(ch: Char): Boolean;
  begin
    IsCharWhiteSpace := (ch = asciisp) or (ch = asciiht) or (ch = asciinl) or (ch = asciicr)
  end; { IsCharWhiteSpace }

  function IsCharQuote(ch: Char): Boolean;
  begin
    IsCharQuote := ch = '"'
  end; { IsCharQuote }

  function IsStringQuoted(str: String): Boolean;
    var
      myresult: Boolean;
      index, limit: Integer;
  begin
    myresult := False;
    index := 0;
    limit := Length(str);
    while not myresult and (index < limit) do
      if IsCharWhiteSpace(str[index + 1]) then
        myresult := True
      else
        Inc(index);
    IsStringQuoted := myresult
  end; { IsStringQuoted }

  function IsStringWithSemicolon(str: String): Boolean;
    var
      myresult: Boolean;
      index, limit: Integer;
  begin
    myresult := False;
    index := 0;
    limit := Length(str);
    while not myresult and (index < limit) do
      if str[index + 1] = ';' then
        myresult := True
      else
        Inc(index);
    IsStringWithSemicolon := myresult
  end; { IsStringWithSemicolon }

  { ***** Token routines ***** }

  procedure TokenListAppendTail(var tokenlist: tokenlisttype; tokenptr: tokenptrtype);
  begin
    with tokenlist, tokenptr^ do
      begin
        prev := tail;
        next := nil;
        if tail = nil then
          head := tokenptr
        else
          tail^.next := tokenptr;
        tail := tokenptr;
        Inc(ecount)
      end
  end; { TokenListAppendTail }

  function TokenListDetachTail(var tokenlist: tokenlisttype): tokenptrtype;
    var
      myresult: tokenptrtype;
  begin
    with tokenlist do
      begin
        myresult := tail;
        tail := tail^.prev;
        if tail = nil then
          head := nil
        else
          tail^.next := nil;
        Dec(ecount)
      end;
    TokenListDetachTail := myresult
  end; { TokenListDetachTail }

  procedure TokenListReset(var tokenlist: tokenlisttype);
    var
      tokenptr: tokenptrtype;
  begin
    with tokenlist do
      while tail <> nil do
        begin
          tokenptr := TokenListDetachTail(tokenlist);
          Dispose(tokenptr)
        end
  end; { TokenListReset }

  procedure TokenListInit(var tokenlist: tokenlisttype);
  begin
    with tokenlist do
      begin
        ecount := 0;
        head := nil;
        tail := nil
      end
  end; { TokenListInit }

  procedure TokenListTerm(var tokenlist: tokenlisttype);
  begin
    TokenListReset(tokenlist)
  end; { TokenListTerm }

  procedure TokenListBuild(var tokenlist: tokenlisttype; str: String);
    var
      index, limit: Integer;
      tokenptr: tokenptrtype;
      eostr: Boolean;
      ch: Char;

    procedure NextTokenCh;
    begin
      if eostr then
        ch := asciinul
      else
        if index = limit then
          begin
            ch := asciinul;
            eostr := True
          end
        else
          begin
            ch := str[index + 1];
            Inc(index)
          end
    end; { NextTokenCh }

  begin
    tokenptr := nil;
    index := 0;
    limit := Length(str);
    eostr := False;
    NextTokenCh;
    while not eostr do
      begin
        while not eostr and IsCharWhiteSpace(ch) do
          NextTokenCh;
        if not eostr then
          begin
            New(tokenptr);
            tokenptr^.tstr := '';
            if IsCharQuote(ch) then
              begin
                NextTokenCh;
                while not eostr and not IsCharQuote(ch) do
                  begin
                    tokenptr^.tstr := tokenptr^.tstr + ch;
                    NextTokenCh
                  end;
                if not eostr then
                  NextTokenCh
              end
            else
              repeat
                tokenptr^.tstr := tokenptr^.tstr + ch;
                NextTokenCh
              until eostr or IsCharWhiteSpace(ch);
            TokenListAppendTail(tokenlist, tokenptr);
            tokenptr := nil
          end
      end;
    if tokenptr <> nil then
      TokenListAppendTail(tokenlist, tokenptr)
  end; { TokenListBuild }

  { ***** Option routines ***** }

  function OptnMatch(str: String): optnxtype;
    var
      myresult: optnxtype;
      b0, b1, probe: Integer;
  begin
    myresult := optnnil;
    b0 := optnmin;
    b1 := optnmax;
    repeat
      probe := (b0 + b1) div 2;
      if str = optnnames[probe] then
        myresult := optntype(probe)
      else
        if str < optnnames[probe] then
          b1 := probe - 1
        else
          b0 := probe + 1
    until (myresult <> optnnil) or (b0 > b1);
    OptnMatch := myresult
  end; { OptnMatch }

  function OptnVerifyParameterList(var tokenlist: tokenlisttype): Boolean;
    var
      myresult: Boolean;
      tokenptr: tokenptrtype;
  begin
    myresult := True;
    tokenptr := tokenlist.head^.next;
    while myresult and (tokenptr <> nil) do
      if OptnMatch(tokenptr^.tstr) < 0 then
        myresult := False
      else
        tokenptr := tokenptr^.next;
    OptnVerifyParameterList := myresult
  end; { OptnVerifyParameterList }

  { ***** Option set routines ***** }

  function OptnSetEncode(optnset: optnsettype): String;
    var
      myresult: String;
      optn: optntype;
      needspace: Boolean;
  begin
    myresult := '[';
    needspace := False;
    for optn := optnmin to optnmax do
      if optn in optnset then
        begin
          if needspace then
            myresult := myresult + ' '
          else
            needspace := True;
          myresult := myresult + optnnames[optn]
        end;
    myresult := myresult + ']';
    OptnSetEncode := myresult;
  end; { OptnSetEncode }

  procedure OptnSetAssignParameterList(
      var optnset: optnsettype; var tokenlist: tokenlisttype; flag: Boolean);
    var
      tokenptr: tokenptrtype;
  begin
    tokenptr := tokenlist.head^.next;
    while tokenptr <> nil do
      begin
        if flag then
          optnset := optnset + [OptnMatch(tokenptr^.tstr)]
        else
          optnset := optnset - [OptnMatch(tokenptr^.tstr)];
        tokenptr := tokenptr^.next
      end
  end; { OptnSetAssignParameterList }

  { ***** Chess clock routines ***** }

  procedure ChessClockReset(var chessclock: chessclocktype);
    var
      color: colorrtype;
  begin
    with chessclock do
      begin
        for color := colorrmin to colorrmax do
          with timervec[color] do
            begin
              TimerReset(timervec[color]);
              countup := False;
              current := 5 * 60 * usectype(1000000)
            end;
        good := startgood;
        evil := startevil
      end
  end; { ChessClockReset }

  procedure ChessClockUpdate(var chessclock: chessclocktype);
    var
      color: colorrtype;
  begin
    with chessclock do
      for color := colorrmin to colorrmax do
        TimerUpdate(timervec[color])
  end; { ChessClockInit }

  function ChessClockIsRunning(var chessclock: chessclocktype): Boolean;
  begin
    with chessclock do
      ChessClockIsRunning := timervec[colorw].running or timervec[colorb].running
  end; { ChessClockIsRunning }

  function ChessClockIsFlagged(var chessclock: chessclocktype): Boolean;
  begin
    with chessclock do
      begin
        ChessClockUpdate(chessclock);
        ChessClockIsFlagged := (timervec[colorw].current = 0) or (timervec[colorb].current = 0)
      end
  end; { ChessClockIsFlagged }

  procedure ChessClockStart(var chessclock: chessclocktype);
  begin
    with chessclock do
      if not ChessClockIsRunning(chessclock) then
        TimerStart(timervec[good])
  end; { ChessClockStart }

  procedure ChessClockStop(var chessclock: chessclocktype);
  begin
    with chessclock do
      if ChessClockIsRunning(chessclock) then
        TimerStop(timervec[good])
  end; { ChessClockStop }

  procedure ChessClockPunch(var chessclock: chessclocktype);
  begin
    with chessclock do
      if not ChessClockIsRunning(chessclock) then
        TimerStart(timervec[good])
      else
        begin
          TimerStop(timervec[good]);
          good := othercolor[good];
          evil := othercolor[evil];
          TimerStart(timervec[good])
        end
  end; { ChessClockPunch }

  function ChessClockRemainingUsecColor(var chessclock: chessclocktype; color: colorrtype): usectype;
  begin
    with chessclock do
      begin
        ChessClockUpdate(chessclock);
        ChessClockRemainingUsecColor := timervec[color].current
      end
  end; { ChessClockRemainingUsecColor }

  function ChessClockRemainingUsec(var chessclock: chessclocktype): usectype;
  begin
    with chessclock do
      ChessClockRemainingUsec := ChessClockRemainingUsecColor(chessclock, good)
  end; { ChessClockRemainingUsec }

  function ChessClockEncode(var chessclock: chessclocktype): String;
    var
      myresult: String;
  begin
    with chessclock do
      begin
        ChessClockUpdate(chessclock);
        myresult := '[' + TimerEncode(timervec[colorw]) + ' ';
        if ChessClockIsRunning(chessclock) then
          if timervec[colorw].running then
            myresult := myresult + '<'
          else
            myresult := myresult + '>'
        else
          myresult := myresult + '=';
        myresult := myresult + ' ' + TimerEncode(timervec[colorb]) + ']';
      end;
    ChessClockEncode := myresult;
  end; { ChessClockEncode }

  { ***** Castling related mapping routines ***** }

  function MapColorMscToCast(color: colorrtype; msc: msctype): casttype;
    var
      myresult: casttype;
  begin
    if color = colorw then
      if msc = msccqs then
        myresult := castwq
      else
        myresult := castwk
    else
      if msc = msccqs then
        myresult := castbq
      else
        myresult := castbk;
    MapColorMscToCast := myresult
  end; { MapColorMscToCast }

  { ***** Simple direction predicate routines ***** }

  function IsDirxOrtho(dir: dirxtype): Boolean; inline;
  begin
    IsDirxOrtho := (dir >= orthodirmin) and (dir <= orthodirmax)
  end; { IsDirxOrtho }

  function IsDirxDiago(dir: dirxtype): Boolean; inline;
  begin
    IsDirxDiago := (dir >= diagodirmin) and (dir <= diagodirmax)
  end; { IsDirxDiago }

  function IsDirxSweep(dir: dirxtype): Boolean; inline;
  begin
    IsDirxSweep := (dir >= sweepdirmin) and (dir <= sweepdirmax)
  end; { IsDirxSweep }

  function IsDirxCrook(dir: dirxtype): Boolean; inline;
  begin
    IsDirxCrook := (dir >= crookdirmin) and (dir <= crookdirmax)
  end; { IsDirxCrook }

  { ***** Simple square/direction calculation routines ***** }

  function CalcBfileDelta(frsq, tosq: sqtype): Integer;
  begin
    CalcBfileDelta := Ord(sqtobfile[tosq]) - Ord(sqtobfile[frsq])
  end; { CalcBfileDelta }

  function CalcBrankDelta(frsq, tosq: sqtype): Integer;
  begin
    CalcBrankDelta := Ord(sqtobrank[tosq]) - Ord(sqtobrank[frsq])
  end; { CalcBrankDelta }

  function CalcAdvance(sq: sqtype; dir: dirtype): sqxtype;
    var
      fval, rval: Integer;
  begin
    fval := Ord(sqtobfile[sq]) + dirtobfiledelta[dir];
    rval := Ord(sqtobrank[sq]) + dirtobrankdelta[dir];
    if (fval < bfilemin) or (fval > bfilemax) or (rval < brankmin) or (rval > brankmax) then
      CalcAdvance := sqnil
    else
      CalcAdvance := bfilebranktosq[fval, rval]
  end; { CalcAdvance }

  function CalcCompass(frsq, tosq: sqtype): dirxtype;
    var
      myresult: dirxtype;
      deltaf, deltar: Integer;
  begin
    myresult := dirnil;
    if frsq <> tosq then
      begin

        deltaf := CalcBfileDelta(frsq, tosq);
        deltar := CalcBrankDelta(frsq, tosq);

        if (myresult = dirnil) and (deltaf > 0) and (deltar = 0) then
          myresult := dire;
        if (myresult = dirnil) and (deltaf = 0) and (deltar > 0) then
          myresult := dirn;
        if (myresult = dirnil) and (deltaf < 0) and (deltar = 0) then
          myresult := dirw;
        if (myresult = dirnil) and (deltaf = 0) and (deltar < 0) then
          myresult := dirs;

        if (myresult = dirnil) and (deltaf > 0) and (deltaf =  deltar) then
          myresult := dirne;
        if (myresult = dirnil) and (deltaf < 0) and (deltaf = -deltar) then
          myresult := dirnw;
        if (myresult = dirnil) and (deltaf < 0) and (deltaf =  deltar) then
          myresult := dirsw;
        if (myresult = dirnil) and (deltaf > 0) and (deltaf = -deltar) then
          myresult := dirse;

        if (myresult = dirnil) and (deltaf =  2) and (deltar =  1) then
          myresult := direne;
        if (myresult = dirnil) and (deltaf =  1) and (deltar =  2) then
          myresult := dirnne;
        if (myresult = dirnil) and (deltaf = -1) and (deltar =  2) then
          myresult := dirnnw;
        if (myresult = dirnil) and (deltaf = -2) and (deltar =  1) then
          myresult := dirwnw;
        if (myresult = dirnil) and (deltaf = -2) and (deltar = -1) then
          myresult := dirwsw;
        if (myresult = dirnil) and (deltaf = -1) and (deltar = -2) then
          myresult := dirssw;
        if (myresult = dirnil) and (deltaf =  1) and (deltar = -2) then
          myresult := dirsse;
        if (myresult = dirnil) and (deltaf =  2) and (deltar = -1) then
          myresult := direse

      end;
    CalcCompass := myresult
  end; { CalcCompass }

  function IsSameBfile(sq0, sq1: sqtype): Boolean; inline;
  begin
    IsSameBfile := sqtobfile[sq0] = sqtobfile[sq1]
  end; { IsSameBfile }

  function IsSameBrank(sq0, sq1: sqtype): Boolean; inline;
  begin
    IsSameBrank := sqtobrank[sq0] = sqtobrank[sq1]
  end; { IsSameBrank }

  function IsInLine(sq0, sq1: sqtype): Boolean; inline;
  begin
    IsInLine := IsDirxSweep(compass[sq0, sq1])
  end; { IsInLine }

  { ***** Simple encoding routines ***** }

  function EncodeDigit(digit: digittype): Char;
  begin
    EncodeDigit := Char(Ord('0') + digit)
  end; { EncodeDigit }

  function EncodeHexDigit(hexdigit: hexdigittype): Char;
    var
      myresult: Char;
  begin
    if (hexdigit >= 0) and (hexdigit < 10) then
      myresult := Char(Ord('0') + hexdigit)
    else
      myresult := Char(Ord('a') + (hexdigit - 10));
    EncodeHexDigit := myresult
  end; { EncodeHexDigit }

  function EncodeInteger(mynumber: Integer): String;
    var
      myresult, stack: String;
      number: Integer;
      digit: digittype;
      index, limit: Integer;
  begin
    number := mynumber;
    if number = 0 then
      myresult := '0'
    else
      begin
        if number > 0 then
          myresult := ''
        else
          begin
            myresult := '-';
            number := -number
          end;
        stack := '';
        while number > 0 do
          begin
            digit := number mod 10;
            number := number div 10;
            stack := stack + EncodeDigit(digit)
          end;
        limit := Length(stack);
        for index := 1 to limit do
          myresult := myresult + stack[limit - index + 1]
      end;
    EncodeInteger := myresult
  end; { EncodeInteger }

  function EncodeLongInt(mynumber: si32type): String;
    var
      myresult, stack: String;
      number: si32type;
      digit: digittype;
      index, limit: Integer;
  begin
    number := mynumber;
    if number = 0 then
      myresult := '0'
    else
      begin
        if number > 0 then
          myresult := ''
        else
          begin
            myresult := '-';
            number := -number
          end;
        stack := '';
        while number > 0 do
          begin
            digit := number mod 10;
            number := number div 10;
            stack := stack + EncodeDigit(digit)
          end;
        limit := Length(stack);
        for index := 1 to limit do
          myresult := myresult + stack[limit - index + 1]
      end;
    EncodeLongInt := myresult
  end; { EncodeLongInt }

  function EncodeUi64Type(mynumber: ui64type): String;
    var
      myresult, stack: String;
      number: ui64type;
      digit: digittype;
      index, limit: Integer;
  begin
    number := mynumber;
    if number = 0 then
      myresult := '0'
    else
      begin
        myresult := '';
        stack := '';
        while number > 0 do
          begin
            digit := number mod 10;
            number := number div 10;
            stack := stack + EncodeDigit(digit)
          end;
        limit := Length(stack);
        for index := 1 to limit do
          myresult := myresult + stack[limit - index + 1]
      end;
    EncodeUi64Type := myresult
  end; { EncodeUi64Type }

  function EncodeCT(count: nctype; usec: usectype): String;
    var
      myresult: String;
      comptime: comptimetype;
      quotient: ui64type;
  begin
    CompTimeLoadFromUsec(comptime, usec);
    myresult := 'Count: ' + EncodeUi64Type(count) + '   Time: ' + CompTimeEncode(comptime);
    if usec > 0 then
      begin
        quotient := Trunc(count / usec * 1.0e+6);
        myresult := myresult + '   Frequency: ' + EncodeUi64Type(quotient)
      end;
    EncodeCT := myresult;
  end; { EncodeCT }

  { ***** Simple encoding routines (chess specific) ***** }

  function EncodeSq(sq: sqxtype): String;
    var
      myresult: String;
  begin
    if sq = sqnil then
      myresult := '-'
    else
      myresult := bfiletochar[sqtobfile[sq]] + branktochar[sqtobrank[sq]];
    EncodeSq := myresult
  end; { EncodeSq }

  function EncodeColor(color: colortype): Char;
  begin
    EncodeColor := colortochar[color]
  end; { EncodeColor }

  function EncodePiece(piece: piecetype): Char;
  begin
    EncodePiece := piecetochar[piece]
  end; { EncodePiece }

  function EncodeMan(man: mantype): Char;
  begin
    EncodeMan := mantochar[man]
  end; { EncodeMan }

  function EncodeManTwoChar(man: mantype): String;
    var
      myresult: String;
  begin
    if man = manvv then
      myresult := '  '
    else
      myresult := EncodeColor(mantocolor[man]) + EncodePiece(mantopiece[man]);
    EncodeManTwoChar := myresult
  end; { EncodeManTwoChar }

  function EncodeCavs(cavs: castsettype): String;
    var
      myresult: String;

    procedure CavsCh(cast: casttype);
    begin
      with cdrvec[cast] do
        if cast in cavs then
          myresult := myresult + cach
    end; { CavsCh }

  begin
    if cavs = [] then
      myresult := '-'
    else
      begin
        myresult := '';
        CavsCh(castwk);
        CavsCh(castwq);
        CavsCh(castbk);
        CavsCh(castbq)
      end;
    EncodeCavs := myresult
  end; { EncodeCavs }

  { ***** Simple decoding routines ***** }

  function IsCharDigit(ch: Char): Boolean;
  begin
    IsCharDigit := (Ord(ch) >= Ord('0')) and (Ord(ch) <= Ord('9'))
  end; { IsCharDigit }

  function DecodeDigit(ch: Char): digittype;
  begin
    DecodeDigit := Ord(ch) - Ord('0')
  end; { DecodeDigit }

  function IsStringAllDigits(str: String): Boolean;
    var
      myresult: Boolean;
      index, limit: Integer;
  begin
    limit := Length(str);
    if limit = 0 then
      myresult := False
    else
      begin
        myresult := True;
        index := 0;
        while myresult and (index < limit) do
          if IsCharDigit(str[index + 1]) then
            Inc(index)
          else
            myresult := False
      end;
    IsStringAllDigits := myresult
  end; { IsStringAllDigits }

  function IsStringUnsignedInteger(str: String): Boolean;
  begin
    IsStringUnsignedInteger := IsStringAllDigits(str) {TBD}
  end; { IsStringUnsignedInteger }

  function DecodeUnsignedInteger(str: String): Integer;
    var
      myresult: Integer;
      index, limit: Integer;
  begin
    myresult := 0;
    limit := Length(str);
    for index := 0 to limit - 1 do
      myresult := (myresult * 10) + DecodeDigit(str[index + 1]);
    DecodeUnsignedInteger := myresult
  end; { DecodeUnsignedInteger }

  function IsStringUi32Type(str: String): Boolean;
  begin
    IsStringUi32Type := IsStringAllDigits(str) {TBD}
  end; { IsStringUi32Type }

  function DecodeUi32Type(str: String): si32type;
    var
      myresult: ui32type;
      index, limit: Integer;
  begin
    myresult := 0;
    limit := Length(str);
    for index := 0 to limit - 1 do
      myresult := (myresult * 10) + DecodeDigit(str[index + 1]);
    DecodeUi32Type := myresult
  end; { DecodeUi32Type }

  { ***** Simple decoding routines (chess specific) ***** }

  function IsCharColor(ch: Char): Boolean;
    var
      myresult: Boolean;
      index: Integer;
  begin
    myresult := False;
    index := 0;
    while not myresult and (index < colorrlen) do
      if ch = colortochar[index] then
        myresult := True
      else
        Inc(index);
    IsCharColor := myresult
  end; { IsCharColor }

  function DecodeColor(ch: Char): colortype;
    var
      myresult: colortype;
      index, match: Integer;
  begin
    match := -1;
    index := 0;
    while (match < 0) and (index < colorrlen) do
      if ch = colortochar[index] then
        match := index
      else
        Inc(index);
    if match >= 0 then
      myresult := colortype(match)
    else
      WTF('DecodeColor fault');
    DecodeColor := myresult
  end; { DecodeColor }

  function IsCharBfile(ch: Char): Boolean;
    var
      myresult: Boolean;
      index: Integer;
  begin
    myresult := False;
    index := 0;
    while not myresult and (index < bfilelen) do
      if ch = bfiletochar[index] then
        myresult := True
      else
        Inc(index);
    IsCharBfile := myresult
  end; { IsCharBfile }

  function DecodeBfile(ch: Char): bfiletype;
    var
      myresult: bfiletype;
      index, match: Integer;
  begin
    match := -1;
    index := 0;
    while (match < 0) and (index < bfilelen) do
      if ch = bfiletochar[index] then
        match := index
      else
        Inc(index);
    if match >= 0 then
      myresult := bfiletype(match)
    else
      WTF('DecodeBfile fault');
    DecodeBfile := myresult
  end; { DecodeBfile }

  function IsCharBrank(ch: Char): Boolean;
    var
      myresult: Boolean;
      index: Integer;
  begin
    myresult := False;
    index := 0;
    while not myresult and (index < branklen) do
      if ch = branktochar[index] then
        myresult := True
      else
        Inc(index);
    IsCharBrank := myresult
  end; { IsCharBrank }

  function DecodeBrank(ch: Char): branktype;
    var
      myresult: branktype;
      index, match: Integer;
  begin
    match := -1;
    index := 0;
    while (match < 0) and (index < branklen) do
      if ch = branktochar[index] then
        match := index
      else
        Inc(index);
    if match >= 0 then
      myresult := branktype(match)
    else
      WTF('DecodeBrank fault');
    DecodeBrank := myresult
  end; { DecodeBrank }

  function IsStringSqx(str: String): Boolean;
    var
      myresult: Boolean;
  begin
    if str = '-' then
      myresult := True
    else
      if Length(str) <> 2 then
        myresult := False
      else
        if not IsCharBfile(str[1]) then
          myresult := False
        else
          if not IsCharBrank(str[2]) then
            myresult := False
          else
            myresult := True;
    IsStringSqx := myresult
  end; { IsStringSqx }

  function DecodeSqx(str: String): sqxtype;
    var
      myresult: sqxtype;
  begin
    if str = '-' then
      myresult := sqnil
    else
      myresult := bfilebranktosq[DecodeBfile(str[1]), DecodeBrank(str[2])];
    DecodeSqx := myresult
  end; { DecodeSqx }

  function IsCharMan(ch: Char): Boolean;
    var
      myresult: Boolean;
      index: Integer;
  begin
    myresult := False;
    index := 0;
    while not myresult and (index < manrlen) do
      if ch = mantochar[index] then
        myresult := True
      else
        Inc(index);
    IsCharMan := myresult
  end; { IsCharMan }

  function DecodeMan(ch: Char): manrtype;
    var
      myresult: mantype;
      index, match: Integer;
  begin
    match := -1;
    index := 0;
    while (match < 0) and (index < manrlen) do
      if ch = mantochar[index] then
        match := index
      else
        Inc(index);
    if match >= 0 then
      myresult := manrtype(match)
    else
      WTF('DecodeMan fault');
    DecodeMan := myresult
  end; { DecodeMan }

  function IsCharCast(ch: Char): Boolean;
    var
      myresult: Boolean;
      index: Integer;
  begin
    myresult := False;
    index := 0;
    while not myresult and (index < castlen) do
      if ch = cdrvec[index].cach then
        myresult := True
      else
        Inc(index);
    IsCharCast := myresult
  end; { IsCharCast }

  function DecodeCast(ch: Char): casttype;
    var
      myresult: casttype;
      index, match: Integer;
  begin
    match := -1;
    index := 0;
    while (match < 0) and (index < castlen) do
      if ch = cdrvec[index].cach then
        match := index
      else
        Inc(index);
    if match >= 0 then
      myresult := casttype(match)
    else
      WTF('DecodeCast fault');
    DecodeCast := myresult
  end; { DecodeCast }

  function IsStringCavs(str: String): Boolean;
    var
      myresult: Boolean;
      index, limit: Integer;
  begin
    if str = '-' then
      myresult := True
    else
      begin
        limit := Length(str);
        if (limit < 1) or (limit > castlen) then
          myresult := False
        else
          begin
            myresult := True;
            index := 0;
            while myresult and (index < limit) do
              if not IsCharCast(str[index + 1]) then
                myresult := False
              else
                Inc(index)
          end
      end;
    IsStringCavs := myresult
  end; { IsStringCavs }

  function DecodeCavs(str: String): castsettype;
    var
      myresult: castsettype;
      index, limit: Integer;
  begin
    myresult := [];
    if str <> '-' then
      begin
        limit := Length(str);
        for index := 0 to limit - 1 do
          myresult := myresult + [DecodeCast(str[index + 1])]
      end;
    DecodeCavs := myresult
  end; { DecodeCavs }

  { ***** Score value routines ***** }

  function IsSvBroken(sv: svtype): Boolean; inline;
  begin
    IsSvBroken := sv = svbroken
  end; { IsSvBroken }

  function IsSvEven(sv: svtype): Boolean; inline;
  begin
    IsSvEven := sv = sveven
  end; { IsSvEven }

  function IsSvCheckmated(sv: svtype): Boolean; inline;
  begin
    IsSvCheckmated := sv = svcheckmated
  end; { IsSvCheckmated }

  function IsSvNegInf(sv: svtype): Boolean; inline;
  begin
    IsSvNegInf := sv = svneginf
  end; { IsSvNegInf }

  function IsSvPosInf(sv: svtype): Boolean; inline;
  begin
    IsSvPosInf := sv = svposinf
  end; { IsSvPosInf }

  function IsSvInfinite(sv: svtype): Boolean; inline;
  begin
    IsSvInfinite := IsSvNegInf(sv) or IsSvPosInf(sv)
  end; { IsSvInfinite }

  function IsSvLosing(sv: svtype): Boolean; inline;
  begin
    IsSvLosing := not IsSvBroken(sv) and (sv <= svlonglose)
  end; { IsSvLosing }

  function IsSvMating(sv: svtype): Boolean; inline;
  begin
    IsSvMating := not IsSvBroken(sv) and (sv >= svlongmate)
  end; { IsSvMating }

  function IsSvLosingOrMating(sv: svtype): Boolean; inline;
  begin
    IsSvLosingOrMating := not IsSvBroken(sv) and ((sv <= svlonglose) or (sv >= svlongmate))
  end; { IsSvLosingOrMating }

  function IsSvInRange(sv: svtype): Boolean; inline;
  begin
    IsSvInRange := (sv > svlonglose) and (sv < svlongmate)
  end; { IsSvInRange }

  function SynthLoseInN(n: Integer): svtype; inline;
  begin
    SynthLoseInN := svlosein0 + n
  end; { SynthLoseInN }

  function SynthMateInN(n: Integer): svtype; inline;
  begin
    SynthMateInN := svmatein1 - n + 1
  end; { SynthMateInN }

  function CalcLosingDistance(sv: svtype): Integer; inline;
  begin
    CalcLosingDistance := sv - svlosein0
  end; { CalcLosingDistance }

  function CalcMatingDistance(sv: svtype): Integer; inline;
  begin
    CalcMatingDistance := svmatein1 - sv + 1
  end; { CalcMatingDistance }

  function EncodeSv(sv: svtype): String;
    var
      myresult: String;

    function EncodeSvIR(sv: svtype): String;
      var
        ip, fp: ui32type;
    begin
      ip := sv div scorefactor;
      fp := (sv mod scorefactor) div 1000;
      EncodeSvIR := EncodeLongInt(ip) + '.' + Format('%.3d', [fp])
    end; { EncodeSvIR }

  begin
    if IsSvBroken(sv) then
      myresult := 'Broken'
    else
      if IsSvInfinite(sv) then
        if IsSvNegInf(sv) then
          myresult := 'NegInf'
        else
          myresult := 'PosInf'
      else
        if IsSvLosingOrMating(sv) then
          if IsSvLosing(sv) then
            if IsSvCheckmated(sv) then
              myresult := 'Checkmated'
            else
              myresult := 'LoseIn' + EncodeInteger(CalcLosingDistance(sv))
          else
            myresult := 'MateIn' + EncodeInteger(CalcMatingDistance(sv))
        else
          if IsSvEven(sv) then
            myresult := ' 0.000'
          else
            if sv < 0 then
              myresult := '-' + EncodeSvIR(-sv)
            else
              myresult := '+' + EncodeSvIR(sv);
    EncodeSv := myresult
  end; { EncodeSv }

  function CalcSvDn(sv: svtype): svtype;
    var
      myresult: svtype;
  begin
    if IsSvBroken(sv) then
      myresult := sv
    else
      if IsSvInRange(sv) then
        myresult := -sv
      else
        if IsSvInfinite(sv) then
          if IsSvNegInf(sv) then
            myresult := svposinf
          else
            myresult := svneginf
        else
          if IsSvLosing(sv) then
            myresult := SynthMateInN(CalcLosingDistance(sv))
          else
            myresult := SynthLoseInN(CalcMatingDistance(sv) - 1);
    CalcSvDn := myresult
  end; { CalcSvDn }

  function CalcSvUp(sv: svtype): svtype;
    var
      myresult: svtype;
  begin
    if IsSvBroken(sv) then
      myresult := sv
    else
      if IsSvInRange(sv) then
        myresult := -sv
      else
        if IsSvInfinite(sv) then
          if IsSvNegInf(sv) then
            myresult := svposinf
          else
            myresult := svneginf
        else
          if IsSvLosing(sv) then
            myresult := SynthMateInN(CalcLosingDistance(sv) + 1)
          else
            myresult := SynthLoseInN(CalcMatingDistance(sv));
    CalcSvUp := myresult
  end; { CalcSvUp }

  { ***** Tablebase score conversion routine ***** }

  function TbBsToScore(tbbs: tbbstype): svtype;
    var
      myresult: svtype;
  begin
    if (tbbs = tbbsunkn) or (tbbs = tbbsresv) or (tbbs = tbbsbust) then
      myresult := svbroken
    else
      if tbbs = tbbsdraw then
        myresult := sveven
      else
        if tbbs < tbbsdraw then
          myresult := SynthLoseInN(tbbs - tbbslose)
        else
          myresult := SynthMateInN(tbbsmate - tbbs + 1);
    TbBsToScore := myresult
  end; { TbBsToScore }

  { ***** Window routines ***** }

  procedure WindowSetFullWidth(var window: windowtype); inline;
  begin
    with window do
      begin
        alfa := svneginf;
        beta := svposinf
      end
  end; { WindowSetFullWidth }

  procedure WindowShiftDn(var window0, window1: windowtype); inline;
  begin
    window1.alfa := CalcSvDn(window0.beta);
    window1.beta := CalcSvDn(window0.alfa)
  end; { WindowShiftDn }

  function WindowIsClosed(var window: windowtype): Boolean; inline;
  begin
    with window do
      WindowIsClosed := alfa >= beta
  end; { WindowIsClosed }

  function WindowIsOpen(var window: windowtype): Boolean; inline;
  begin
    with window do
      WindowIsOpen := alfa < beta
  end; { WindowIsOpen }

  function WindowIsPvNode(var window: windowtype): Boolean; inline;
  begin
    with window do
      WindowIsPvNode := (beta - alfa) > 1
  end; { WindowIsPvNode }

  function WindowIsZeroWidth(var window: windowtype): Boolean; inline;
  begin
    with window do
      WindowIsZeroWidth := (beta - alfa) = 1
  end; { WindowIsZeroWidth }

  function WindowEncode(var window: windowtype): String;
  begin
    with window do
      WindowEncode := '[' + EncodeSv(alfa) + ' ' + EncodeSv(beta) + ']'
  end; { WindowEncode }

  { ***** One side material signature routines ***** }

  function OsMsigCountPiece(osmsig: osmsigtype; piece: piecertype): cctype;
  begin
    OsMsigCountPiece := (osmsig shr (piece * 4)) and 15
  end; { OsMsigCountPiece }

  procedure OsMsigClearPiece(var osmsig: osmsigtype; piece: piecertype);
  begin
    Dec(osmsig, (OsMsigCountPiece(osmsig, piece) * osmsigdeltavec[piece]))
  end; { OsMsigClearPiece }

  function OsMsigFirstPiece(osmsig: osmsigtype): piecetype;
    var
      myresult: piecetype;
      piece: piecetype;
  begin
    myresult := piecev;
    piece := piecep;
    while (myresult = piecev) and (piece <= piecermax) do
      if OsMsigCountPiece(osmsig, piece) > 0 then
        myresult := piece
      else
        Inc(piece);
    OsMsigFirstPiece := myresult
  end; { OsMsigFirstPiece }

  { ***** One side material signature vector routines ***** }

  function OsMsigVecEqual(var osmsigvec0, osmsigvec1: osmsigvectype): Boolean;
  begin
    OsMsigVecEqual :=
        (osmsigvec0[colorw] = osmsigvec1[colorw]) and
        (osmsigvec0[colorb] = osmsigvec1[colorb])
  end; { OsMsigVecEqual }

  { ***** Material signature routines ***** }

  procedure MsigLoadFromOsMsigVec(var msig: msigtype; var osmsigvec: osmsigvectype);
  begin
    msig := ui64type(osmsigvec[colorw]) + (ui64type(osmsigvec[colorb]) shl (piecerlen * 4))
  end; { MsigLoadFromOsMsigVec }

  function MsigCountMan(msig: msigtype; man: manrtype): cctype;
  begin
    MsigCountMan := (msig shr (man * 4)) and 15
  end; { MsigCountMan }

  function MsigCount(msig: msigtype): cctype;
    var
      myresult: cctype;
      man: manrtype;
  begin
    myresult := 0;
    for man := manrmin to manrmax do
      Inc(myresult, MsigCountMan(msig, man));
    MsigCount := myresult
  end; { MsigCount }

  function MsigName(msig: msigtype): String;
    var
      myresult: String;
      man: manrtype;
      cc: cctype;
      index: Integer;
      ch: Char;
  begin
    myresult := '';
    for man := manwk downto manwp do
      begin
        cc := MsigCountMan(msig, man);
        if cc > 0 then
          begin
            ch := piecetochar[mantopiece[man]];
            for index := 0 to cc - 1 do
              myresult := myresult + ch
          end
      end;
    for man := manbk downto manbp do
      begin
        cc := MsigCountMan(msig, man);
        if cc > 0 then
          begin
            ch := piecetochar[mantopiece[man]];
            for index := 0 to cc - 1 do
              myresult := myresult + ch
          end
      end;
    MsigName := myresult
  end; { MsigName }

  function MsigCalcOther(msig: msigtype): msigtype;
    var
      myresult: msigtype;
      man: manrtype;
  begin
    myresult := 0;
    for man := manrmin to manrmax do
      Inc(myresult, (MsigCountMan(msig, otherman[man]) * msigdeltavec[man]));
    MsigCalcOther := myresult
  end; { MsigCalcOther }

  { ***** Census routines ***** }

  procedure CensusReset(var census: censustype);
    var
      color: colortype;
      man: mantype;
  begin
    with census do
      begin
        for color := colorrmin to colorrmax do
          cic[color] := 0;
        for man := manrmin to manrmax do
          mic[man] := 0
      end
  end; { CensusReset }

  procedure CensusLoad(var census: censustype; var board: boardtype);
    var
      sq: sqtype;
      man: mantype;
  begin
    with census, board do
      begin
        CensusReset(census);
        for sq := sqmin to sqmax do
          begin
            man := sqv[sq];
            if man <> manvv then
              begin
                Inc(cic[mantocolor[man]]);
                Inc(mic[man])
              end
          end
      end
  end; { CensusLoad }

  function CensusForceColor(var census: censustype; color: colorrtype): Boolean;
    var
      myresult: Boolean;
      bcount, ncount: cctype;
  begin
    with census do
      begin
        if mic[synthpawn[color]] > 0 then
          myresult := True
        else
          if mic[synthrook[color]] > 0 then
            myresult := True
          else
            if mic[synthqueen[color]] > 0 then
              myresult := True
            else
              begin
                bcount := mic[synthbishop[color]];
                if bcount > 1 then
                  myresult := True
                else
                  begin
                    ncount := mic[synthknight[color]];
                    if (bcount = 1) and (ncount > 0) then
                      myresult := True
                    else
                      myresult := ncount > 2
                  end
              end
      end;
    CensusForceColor := myresult
  end; { CensusForceColor }

  function CensusForce(var census: censustype): Boolean;
  begin
    CensusForce := CensusForceColor(census, colorw) or CensusForceColor(census, colorb)
  end; { CensusForce }

  function CensusIsValid(var census: censustype): Boolean;

    function CensusIsValidColor(color: colorrtype): Boolean;
      var
        myresult: Boolean;
        piece: piecertype;
        cpv: array [piecertype] of cctype;
        surplus: Integer;
    begin
      with census do
        begin
          for piece := piecermin to piecermax do
            cpv[piece] := mic[colorpiecetoman[color, piece]];
          if cpv[piecek] <> 1 then
            myresult := False
          else
            if cpv[piecep] > bfilelen then
              myresult := False
            else
              begin
                surplus := bfilelen - cpv[piecep];
                if cpv[pieceq] > 1 then
                  Dec(surplus, (cpv[pieceq] - 1));
                if cpv[piecer] > 2 then
                  Dec(surplus, (cpv[piecer] - 2));
                if cpv[pieceb] > 2 then
                  Dec(surplus, (cpv[pieceb] - 2));
                if cpv[piecen] > 2 then
                  Dec(surplus, (cpv[piecen] - 2));
                myresult := surplus >= 0
              end
        end;
      CensusIsValidColor := myresult
    end; { CensusIsValidColor }

  begin
    CensusIsValid := CensusIsValidColor(colorw) and CensusIsValidColor(colorb)
  end; { CensusIsValid }

  { ***** Board routines ***** }

  procedure BoardReset(var board: boardtype);
    var
      sq: sqtype;
  begin
    with board do
      for sq := sqmin to sqmax do
        sqv[sq] := manvv
  end; { BoardReset }

  function BoardLocateKing(var board: boardtype; color: colortype): sqxtype;
    var
      myresult: sqxtype;
      sq: sqtype;
      sqindex: Integer;
      kingman: manrtype;
  begin
    with board do
      begin
        myresult := sqnil;
        kingman := synthking[color];
        sqindex := 0;
        while (myresult = sqnil) and (sqindex < sqlen) do
          begin
            sq := sqtype(sqindex);
            if sqv[sq] = kingman then
              myresult := sq
            else
              Inc(sqindex)
          end
      end;
    BoardLocateKing := myresult
  end; { BoardLocateKing }

  function BoardEncodeGraphicMono(var board: boardtype): String;
    var
      myresult: String;
      bfile: bfiletype;
      brank: branktype;
      sq: sqtype;
      man: mantype;
  begin
    with board do
      begin
        myresult := '';
        for brank := brankmax downto brankmin do
          begin
            for bfile := bfilemin to bfilemax do
              begin
                sq := bfilebranktosq[bfile, brank];
                man := sqv[sq];
                if man = manvv then
                  if sqtocolor[sq] = colorw then
                    myresult := myresult + '  '
                  else
                    myresult := myresult + '::'
                else
                  myresult := myresult + EncodeManTwoChar(man)
              end;
            myresult := myresult + asciinl
          end
      end;
    BoardEncodeGraphicMono := myresult
  end; { BoardEncodeGraphicMono }

  function BoardEncodeGraphicColorSq(var board: boardtype; sq: sqtype): String;
    var
      myresult: String;
      man: mantype;

    procedure AnsiSeq(str: string);
    begin
      myresult := myresult + asciiesc + '[' + str + 'm'
    end; { AnsiSeq }

  begin
    myresult := '';
    if sqtocolor[sq] = colorw then
      AnsiSeq('47')
    else
      AnsiSeq('42');
    man := board.sqv[sq];
    if man <> manvv then
      if mantocolor[man] = colorw then
        AnsiSeq('31')
      else
        AnsiSeq('34');
    myresult := myresult + EncodeManTwoChar(man);
    AnsiSeq('0');
    BoardEncodeGraphicColorSq := myresult
  end; { BoardEncodeGraphicColorSq }

  function BoardEncodeGraphicColor(var board: boardtype): String;
    var
      myresult: String;
      bfile: bfiletype;
      brank: branktype;
      sq: sqtype;
  begin
    with board do
      begin
        myresult := '';
        for brank := brankmax downto brankmin do
          begin
            for bfile := bfilemin to bfilemax do
              begin
                sq := bfilebranktosq[bfile, brank];
                myresult := myresult + BoardEncodeGraphicColorSq(board, sq)
              end;
            myresult := myresult + asciinl
          end
      end;
    BoardEncodeGraphicColor := myresult
  end; { BoardEncodeGraphicColor }

  function BoardEncode(var board: boardtype): mpdtype;
    var
      myresult: mpdtype;
      bfile: bfiletype;
      brank: branktype;
      man: mantype;
      spaces: Integer;
  begin

    { MPD encoding }

    myresult := '';
    with board do
      begin
        for brank := brankmax downto brankmin do
          begin
            spaces := 0;
            for bfile := bfilemin to bfilemax do
              begin
                man := rfv[brank, bfile];
                if man = manvv then
                  Inc(spaces)
                else
                  begin
                    if spaces > 0 then
                      begin
                        myresult := myresult + EncodeDigit(spaces);
                        spaces := 0
                      end;
                    myresult := myresult + EncodeMan(man);
                  end
              end;
            if spaces > 0 then
              myresult := myresult + EncodeDigit(spaces);
            if brank <> brank1 then
              myresult := myresult + '/'
          end
      end;
    BoardEncode := myresult
  end; { BoardEncode }

  function BoardDecode(var board: boardtype; str: String): Boolean;
    var
      myresult: Boolean;
      index, limit: Integer;
      ch: Char;
      bfindex, brindex: Integer;
      digit: digittype;

    procedure PutMan(man: mantype);
    begin
      board.rfv[brindex, bfindex] := man;
      Inc(bfindex)
    end; { PutMan }

    procedure PutVacant;
    begin
      PutMan(manvv)
    end; { PutVacant }

    procedure PutVacantSeq;
    begin
      while bfindex < bfilelen do
        PutVacant
    end; { PutVacantSeq }

  begin

    { MPD decoding }

    with board do
      begin
        myresult := True;
        index := 0;
        limit := Length(str);
        brindex := brankmax;
        bfindex := bfilemin;

        { Loop once per input character }

        while myresult and (index < limit) do
          begin
            ch := str[index + 1];
            Inc(index);
            if ch = '/' then
              begin
                if brindex = brankmin then
                  myresult := False
                else
                  begin
                    PutVacantSeq;
                    Dec(brindex);
                    bfindex := bfilemin
                  end
              end
            else
              if IsCharDigit(ch) then
                begin
                  if bfindex = bfilelen then
                    myresult := False
                  else
                    begin
                      digit := DecodeDigit(ch);
                      if (digit < 1) or (digit > bfilelen) then
                        myresult := False
                      else
                        if (digit + bfindex) > bfilelen then
                          myresult := False
                        else
                          while digit > 0 do
                            begin
                              PutVacant;
                              Dec(digit)
                            end
                    end
                end
              else
                if IsCharMan(ch) then
                  if bfindex = bfilelen then
                    myresult := False
                  else
                    PutMan(DecodeMan(ch))
                else
                  myresult := False
          end;

        { Finalize }

        if myresult then
          if brindex <> brankmin then
            myresult := False
          else
            PutVacantSeq;
        if not myresult then
          BoardReset(board)
      end;
    BoardDecode := myresult
  end; { BoardDecode }

  function BoardCountAttacks(var board: boardtype; color: colorrtype; tosq: sqtype): cctype;
    var
      myresult: cctype;
      dir: dirtype;
      frsq: sqxtype;
      man: mantype;
      manset: mansettype;
      stopped: Boolean;
  begin
    with board do
      begin
        myresult := 0;

        { Knight attacks }

        manset := [synthknight[color]];
        for dir := crookdirmin to crookdirmax do
          begin
            frsq := advance[tosq, dir];
            if frsq <> sqnil then
              if sqv[frsq] in manset then
                Inc(myresult)
          end;

        { Other attacks }

        for dir := sweepdirmin to sweepdirmax do
          begin
            frsq := advance[tosq, dir];
            if frsq <> sqnil then
              begin
                man := sqv[frsq];
                if man in manatk0setvec[color, dir] then
                  Inc(myresult)
                else
                  if man = manvv then
                    begin
                      manset := manatk1setvec[color, dir];
                      stopped := False;
                      while not stopped do
                        begin
                          frsq := advance[frsq, dir];
                          if frsq = sqnil then
                            stopped := True
                          else
                            begin
                              man := sqv[frsq];
                              if man <> manvv then
                                stopped := True;
                              if man in manset then
                                Inc(myresult)
                            end
                        end
                    end
              end
          end
      end;
    BoardCountAttacks := myresult
  end; { BoardCountAttacks }

  function BoardIsValidCensus(var board: boardtype): Boolean;
    var
      census: censustype;
  begin
    CensusLoad(census, board); BoardIsValidCensus := CensusIsValid(census)
  end; { BoardIsValidCensus }

  function BoardIsValidPawnPlacement(var board: boardtype): Boolean;
    var
      myresult: Boolean;
      index: Integer;
      bfile: bfiletype;
  begin
    with board do
      begin
        myresult := True;
        index := 0;
        while myresult and (index < bfilelen) do
          begin
            bfile := bfiletype(index);
            if (rfv[brank1, bfile] in pawnmanset) or (rfv[brank8, bfile] in pawnmanset) then
              myresult := False
            else
              Inc(index)
          end
      end;
    BoardIsValidPawnPlacement := myresult
  end; { BoardIsValidPawnPlacement }

  function BoardIsValidKingPlacement(var board: boardtype; good: colorrtype): Boolean;
    var
      evil: colorrtype;
  begin
    evil := othercolor[good];
    BoardIsValidKingPlacement :=
      (BoardCountAttacks(board, good, BoardLocateKing(board, evil)) = 0) and
      (BoardCountAttacks(board, evil, BoardLocateKing(board, good)) < 3)
  end; { BoardIsValidKingPlacement }

  function BoardIsValidCastling(var board: boardtype; cavs: castsettype): Boolean;
    var
      myresult: Boolean;
      index: Integer;
  begin
    with board do
      begin
        myresult := True;
        index := 0;
        while myresult and (index < castlen) do
          with cdrvec[index] do
            begin
              if index in cavs then
                if (sqv[k0sq] <> kman) or (sqv[r0sq] <> rman) then
                  myresult := False;
              Inc(index)
            end
      end;
    BoardIsValidCastling := myresult
  end; { BoardIsValidCastling }

  function BoardIsValidEnPassant(var board: boardtype; good: colorrtype; epsq: sqxtype): Boolean;
    var
      myresult: Boolean;
  begin
    with board do
      if epsq = sqnil then
        myresult := True
      else
        if epranktogood[sqtobrank[epsq]] <> good then
          myresult := False
        else
          if sqv[epsq] <> manvv then
            myresult := False
          else
            if sqv[advance[epsq, pawnadvdir[good]]] <> manvv then
              myresult := False
            else
              myresult := sqv[advance[epsq, pawnretdir[good]]] = synthpawn[othercolor[good]];
    BoardIsValidEnPassant := myresult
  end; { BoardIsValidEnPassant }

  function BoardIsValid(
      var board: boardtype; good: colorrtype; cavs: castsettype; epsq: sqxtype): Boolean;
    var
      myresult: Boolean;
  begin
    if not BoardIsValidCensus(board) then
      myresult := False
    else
      if not BoardIsValidPawnPlacement(board) then
        myresult := False
      else
        if not BoardIsValidKingPlacement(board, good) then
          myresult := False
        else
          if not BoardIsValidCastling(board, cavs) then
            myresult := False
          else
            if not BoardIsValidEnPassant(board, good, epsq) then
              myresult := False
            else
              myresult := True;
    BoardIsValid := myresult
  end; { BoardIsValid }

  { ***** Bitboard routines ***** }

  procedure BbReset(var bb: bbtype); inline;
  begin
    with bb do
      bv64 := 0
  end; { BbReset }

  function BbIsReset(var bb: bbtype): Boolean; inline;
  begin
    with bb do
      BbIsReset := bv64 = 0
  end; { BbIsReset }

  procedure BbSetSq(var bb: bbtype; sq: sqtype); inline;
  begin
    with bb do
      bv64 := bv64 or singlebitbbvec[sq].bv64
  end; { BbSetSq }

  procedure BbResetSq(var bb: bbtype; sq: sqtype); inline;
  begin
    with bb do
      bv64 := bv64 and cancelbitbbvec[sq].bv64
  end; { BbResetSq }

  function BbTestSq(var bb: bbtype; sq: sqtype): Boolean; inline;
  begin
    with bb do
      BbTestSq := (bv64 and singlebitbbvec[sq].bv64) <> 0
  end; { BbTestSq }

  function BbEqual(var bbop0, bbop1: bbtype): Boolean; inline;
  begin
    BbEqual := bbop0.bv64 = bbop1.bv64
  end; { BbEqual }

  procedure BbNot1(var bbres, bbop0: bbtype); inline;
  begin
    with bbres do
      bv64 := not bbop0.bv64
  end; { BbNot1 }

  procedure BbAnd2(var bbres, bbop0, bbop1: bbtype); inline;
  begin
    with bbres do
      bv64 := bbop0.bv64 and bbop1.bv64
  end; { BbAnd2 }

  procedure BbAnd2D(var bbres, bbop0: bbtype); inline;
  begin
    with bbres do
      bv64 := bv64 and bbop0.bv64
  end; { BbAnd2D }

  procedure BbAnd2C2(var bbres, bbop0, bbop1: bbtype); inline;
  begin
    with bbres do
      bv64 := bbop0.bv64 and not bbop1.bv64
  end; { BbAnd2C2 }

  procedure BbAnd2C2D(var bbres, bbop0: bbtype); inline;
  begin
    with bbres do
      bv64 := bv64 and not bbop0.bv64
  end; { BbAnd2C2D }

  procedure BbAnd3(var bbres, bbop0, bbop1, bbop2: bbtype); inline;
  begin
    with bbres do
      bv64 := bbop0.bv64 and bbop1.bv64 and bbop2.bv64
  end; { BbAnd3 }

  procedure BbIor2(var bbres, bbop0, bbop1: bbtype); inline;
  begin
    with bbres do
      bv64 := bbop0.bv64 or bbop1.bv64
  end; { BbIor2 }

  procedure BbIor2D(var bbres, bbop0: bbtype); inline;
  begin
    with bbres do
      bv64 := bv64 or bbop0.bv64
  end; { BbIor2D }

  procedure BbXor2D(var bbres, bbop0: bbtype); inline;
  begin
    with bbres do
      bv64 := bv64 xor bbop0.bv64
  end; { BbXor2D }

  function BbNI2(var bbop0, bbop1: bbtype): Boolean; inline;
  begin
    BbNI2 := (bbop0.bv64 and bbop1.bv64) = 0
  end; { BbNI2 }

  function BbNI3(var bbop0, bbop1, bbop2: bbtype): Boolean; inline;
  begin
    BbNI3 := (bbop0.bv64 and bbop1.bv64 and bbop2.bv64) = 0
  end; { BbNI3 }

  function BbCount(var bb: bbtype): cctype; inline;
    var
      myresult: cctype;
      bbw: bbwtype;
  begin
    with bb do
      begin
        myresult := 0;
        for bbw := bbwmin to bbwmax do
          myresult := myresult + bitcountvec[wvec[bbw]]
      end;
    BbCount := myresult
  end; { BbCount }

  function BbFirstSq(var bb: bbtype): sqxtype; inline;
    var
      myresult: sqxtype;
      bbwindex: Integer;
      wordfirstbit: Integer;
  begin
    with bb do
      begin
        myresult := sqnil;
        bbwindex := 0;
        while (myresult = sqnil) and (bbwindex < bbwlen) do
          begin
            wordfirstbit := bitfirstvec[wvec[bbwindex]];
            if wordfirstbit >= 0 then
              myresult := sqxtype(wordfirstbit + (bbwindex * bbwbitlen))
            else
              Inc(bbwindex)
          end
      end;
    BbFirstSq := myresult
  end; { BbFirstSq }

  function BbNextSq(var bb: bbtype): sqxtype; inline;
    var
      myresult: sqxtype;
      bbwindex: Integer;
      wordfirstbit: Integer;
  begin
    with bb do
      begin
        myresult := sqnil;
        bbwindex := 0;
        while (myresult = sqnil) and (bbwindex < bbwlen) do
          begin
            wordfirstbit := bitfirstvec[wvec[bbwindex]];
            if wordfirstbit >= 0 then
              begin
                myresult := sqxtype(wordfirstbit + (bbwindex * bbwbitlen));
                wvec[bbwindex] := wvec[bbwindex] xor (1 shl wordfirstbit)
              end
            else
              Inc(bbwindex)
          end
      end;
    BbNextSq := myresult
  end; { BbNextSq }

  function BbEncodeBits(var bb: bbtype): String;
    var
      myresult: String;
      sq: sqtype;
  begin
    myresult := '[';
    for sq := sqmin to sqmax do
      if BbTestSq(bb, sq) then
        myresult := myresult + '1'
      else
        myresult := myresult + '0';
    myresult := myresult + ']';
    BbEncodeBits := myresult
  end; { BbEncodeBits }

  function BbEncodeSqs(var bb: bbtype): String;
    var
      myresult: String;
      scanbb: bbtype;
      scansq: sqxtype;
      needspace: Boolean;
  begin
    myresult := '[';
    needspace := False;
    scanbb := bb;
    repeat
      scansq := bBNextSq(scanbb);
      if scansq <> sqnil then
        begin
          if needspace then
            myresult := myresult + ' ';
          myresult := myresult + EncodeSq(scansq);
          needspace := True
        end
    until scansq = sqnil;
    myresult := myresult + ']';
    BbEncodeSqs := myresult
  end; { BbEncodeSqs }

  { ***** Bitboard database routines ***** }

  procedure BbdbReset(var bbdb: bbdbtype);
    var
      color: colortype;
      man: mantype;
      sq: sqtype;
  begin
    with bbdb do
      begin
        BbReset(merge);
        BbReset(sweep);
        for color := colorrmin to colorrmax do
          begin
            BbReset(locbc[color]);
            BbReset(atkbc[color])
          end;
        for man := manrmin to manrmax do
          BbReset(locbm[man]);
        for sq := sqmin to sqmax do
          begin
            BbReset(atkfs[sq]);
            BbReset(atkts[sq])
          end
      end
  end; { BbdbReset }

  procedure BbdbAddAttacks(var bbdb: bbdbtype; sq: sqtype; man: manrtype);
    var
      color: colorrtype;
      dir: dirtype;
      atkfrbb: bbtype;
      atkfrsq: sqxtype;
      dir0, dir1: dirtype;
      scansq: sqxtype;
      stopbb: bbtype;
      delta: si8type;
  begin
    with bbdb do
      begin
        color := mantocolor[man];

        { Generate the attacks-from-square bitboard }

        case mantopiece[man] of
          piecep:
            atkfrbb := pawnatkbbvec[color, sq];
          piecen:
            atkfrbb := knightatkbbvec[sq];
          pieceb, piecer, pieceq:
            begin
              BbReset(atkfrbb);
              dir0 := mantodir0[man];
              dir1 := mantodir1[man];
              for dir := dir0 to dir1 do
                if onboard[sq, dir] then
                  begin
                    BbIor2(stopbb, merge, edgebbvec[dir]);
                    delta := dirtosqdelta[dir];
                    scansq := sq;
                    repeat
                      Inc(scansq, delta);
                      BbSetSq(atkfrbb, scansq)
                    until BbTestSq(stopbb, scansq)
                  end
            end;
          piecek:
            atkfrbb := kingatkbbvec[sq]
        end; { case }

        { Apply the attacks-from-square bitboard }

        atkfs[sq] := atkfrbb;
        BbIor2D(atkbc[color], atkfrbb);
        repeat
          atkfrsq := BbNextSq(atkfrbb);
          if atkfrsq <> sqnil then
            BbSetSq(atkts[atkfrsq], sq)
        until atkfrsq = sqnil
      end
  end; { BbdbAddAttacks }

  procedure BbdbDelAttacks(var bbdb: bbdbtype; sq: sqtype; man: manrtype);
    var
      color: colorrtype;
      atkfrbb: bbtype;
      atkfrsq: sqxtype;
  begin
    with bbdb do
      begin
        color := mantocolor[man];
        atkfrbb := atkfs[sq];
        BbReset(atkfs[sq]);
        repeat
          atkfrsq := BbNextSq(atkfrbb);
          if atkfrsq <> sqnil then
            begin
              BbResetSq(atkts[atkfrsq], sq);
              if BbNI2(locbc[color], atkts[atkfrsq]) then
                BbResetSq(atkbc[color], atkfrsq)
            end
        until atkfrsq = sqnil
      end
  end; { BbdbDelAttacks }

  procedure BbdbProAttacks(var bbdb: bbdbtype; sq: sqtype);
    var
      atktobb: bbtype;
      atktosq: sqxtype;
      color: colorrtype;
      scansq: sqxtype;
      dir: dirtype;
      stopbb: bbtype;
      delta: si8type;
  begin
    with bbdb do
      begin
        BbAnd2(atktobb, atkts[sq], sweep);
        repeat
          atktosq := BbNextSq(atktobb);
          if atktosq <> sqnil then
            begin
              dir := compass[atktosq, sq];
              if onboard[sq, dir] then
                begin
                  if BbTestSq(locbc[colorw], atktosq) then
                    color := colorw
                  else
                    color := colorb;
                  BbIor2(stopbb, merge, edgebbvec[dir]);
                  delta := dirtosqdelta[dir];
                  scansq := sq;
                  repeat
                    Inc(scansq, delta);
                    BbSetSq(atkfs[atktosq], scansq);
                    BbSetSq(atkts[scansq], atktosq);
                    BbSetSq(atkbc[color], scansq)
                  until BbTestSq(stopbb, scansq)
                end
            end
        until atktosq = sqnil
      end
  end; { BbdbProAttacks }

  procedure BbdbCutAttacks(var bbdb: bbdbtype; sq: sqtype);
    var
      atktobb: bbtype;
      atktosq: sqxtype;
      color: colorrtype;
      scansq: sqxtype;
      dir: dirtype;
      stopbb: bbtype;
      delta: si8type;
  begin
    with bbdb do
      begin
        BbAnd2(atktobb, atkts[sq], sweep);
        repeat
          atktosq := BbNextSq(atktobb);
          if atktosq <> sqnil then
            begin
              dir := compass[atktosq, sq];
              if onboard[sq, dir] then
                begin
                  if BbTestSq(locbc[colorw], atktosq) then
                    color := colorw
                  else
                    color := colorb;
                  BbIor2(stopbb, merge, edgebbvec[dir]);
                  delta := dirtosqdelta[dir];
                  scansq := sq;
                  repeat
                    Inc(scansq, delta);
                    BbResetSq(atkfs[atktosq], scansq);
                    BbResetSq(atkts[scansq], atktosq);
                    if BbNI2(locbc[color], atkts[scansq]) then
                      BbResetSq(atkbc[color], scansq)
                  until BbTestSq(stopbb, scansq)
                end
            end
        until atktosq = sqnil
      end
  end; { BbdbCutAttacks }

  procedure BbdbLocusToggle(var bbdb: bbdbtype; man: manrtype; sq: sqtype);
    var
      bb: bbtype;
  begin
    with bbdb do
      begin
        bb := singlebitbbvec[sq];
        BbXor2D(merge, bb);
        BbXor2D(locbc[mantocolor[man]], bb);
        BbXor2D(locbm[man], bb);
        if man in sweepermanset then
          BbXor2D(sweep, bb)
      end
  end; { BbdbLocusToggle }

  procedure BbdbLocusChange(var bbdb: bbdbtype; man: manrtype; frsq, tosq: sqtype);
    var
      bb: bbtype;
  begin
    with bbdb do
      begin
        bb := doublebitbbvec[frsq, tosq];
        BbXor2D(merge, bb);
        BbXor2D(locbc[mantocolor[man]], bb);
        BbXor2D(locbm[man], bb);
        if man in sweepermanset then
          BbXor2D(sweep, bb)
      end
  end; { BbdbLocusChange }

  procedure BbdbAddMan(var bbdb: bbdbtype; man: manrtype; sq: sqtype);
  begin

    { Update locus }

    BbdbLocusToggle(bbdb, man, sq);

    { Update attacks }

    BbdbCutAttacks(bbdb, sq);
    BbdbAddAttacks(bbdb, sq, man)

  end; { BbdbAddMan }

  procedure BbdbDelMan(var bbdb: bbdbtype; man: manrtype; sq: sqtype);
  begin

    { Update locus }

    BbdbLocusToggle(bbdb, man, sq);

    { Update attacks }

    BbdbDelAttacks(bbdb, sq, man);
    BbdbProAttacks(bbdb, sq)

  end; { BbdbDelMan }

  procedure BbdbMovMan(var bbdb: bbdbtype; man: manrtype; frsq, tosq: sqtype);
  begin

    { Update locus }

    BbdbLocusChange(bbdb, man, frsq, tosq);

    { Update attacks }

    BbdbDelAttacks(bbdb, frsq, man);
    BbdbProAttacks(bbdb, frsq);
    BbdbCutAttacks(bbdb, tosq);
    BbdbAddAttacks(bbdb, tosq, man)

  end; { BbdbMovMan }

  procedure BbdbCaptureMan(var bbdb: bbdbtype; frman, toman: manrtype; frsq, tosq: sqtype);
  begin

    { Update locus }

    BbdbLocusToggle(bbdb, toman, tosq);
    BbdbLocusChange(bbdb, frman, frsq, tosq);

    { Update attacks }

    BbdbDelAttacks(bbdb, tosq, toman);
    BbdbDelAttacks(bbdb, frsq, frman);
    BbdbProAttacks(bbdb, frsq);
    BbdbAddAttacks(bbdb, tosq, frman)

  end; { BbdbCaptureMan }

  procedure BbdbRevCaptMan(var bbdb: bbdbtype; frman, toman: manrtype; frsq, tosq: sqtype);
  begin

    { Update locus }

    BbdbLocusChange(bbdb, frman, tosq, frsq);
    BbdbLocusToggle(bbdb, toman, tosq);

    { Update attacks }

    BbdbDelAttacks(bbdb, tosq, frman);
    BbdbCutAttacks(bbdb, frsq);
    BbdbAddAttacks(bbdb, frsq, frman);
    BbdbAddAttacks(bbdb, tosq, toman)

  end; { BbdbRevCaptMan }

  procedure BbdbWriteBits(var bbdb: bbdbtype; var ofile: Text);
    var
      color: colortype;
      man: mantype;
      sq: sqtype;
  begin
    with bbdb do
      begin
        WriteStrNL(ofile, 'merge     ' + BbEncodeBits(merge));
        WriteStrNL(ofile, 'sweep     ' + BbEncodeBits(sweep));
        for color := colorrmin to colorrmax do
          WriteStrNL(ofile, 'locbc[' + EncodeColor(color) + ']  ' + BbEncodeBits(locbc[color]));
        for man := manrmin to manrmax do
          WriteStrNL(ofile, 'locbm[' + EncodeManTwoChar(man) + '] ' + BbEncodeBits(locbm[man]));
        for color := colorrmin to colorrmax do
          WriteStrNL(ofile, 'atkbc[' + EncodeColor(color) + ']  ' + BbEncodeBits(atkbc[color]));
        for sq := sqmin to sqmax do
          WriteStrNL(ofile, 'atkfs[' + EncodeSq(sq) + '] ' + BbEncodeBits(atkfs[sq]));
        for sq := sqmin to sqmax do
          WriteStrNL(ofile, 'atkts[' + EncodeSq(sq) + '] ' + BbEncodeBits(atkts[sq]))
      end
  end; { BbdbWriteBits }

  procedure BbdbWriteSqs(var bbdb: bbdbtype; var ofile: Text);
    var
      color: colortype;
      man: mantype;
      sq: sqtype;
  begin
    with bbdb do
      begin
        WriteStrNL(ofile, 'merge     ' + BbEncodeSqs(merge));
        WriteStrNL(ofile, 'sweep     ' + BbEncodeSqs(sweep));
        for color := colorrmin to colorrmax do
          WriteStrNL(ofile, 'locbc[' + EncodeColor(color) + ']  ' + BbEncodeSqs(locbc[color]));
        for man := manrmin to manrmax do
          WriteStrNL(ofile, 'locbm[' + EncodeManTwoChar(man) + '] ' + BbEncodeSqs(locbm[man]));
        for color := colorrmin to colorrmax do
          WriteStrNL(ofile, 'atkbc[' + EncodeColor(color) + ']  ' + BbEncodeSqs(atkbc[color]));
        for sq := sqmin to sqmax do
          WriteStrNL(ofile, 'atkfs[' + EncodeSq(sq) + '] ' + BbEncodeSqs(atkfs[sq]));
        for sq := sqmin to sqmax do
          WriteStrNL(ofile, 'atkts[' + EncodeSq(sq) + '] ' + BbEncodeSqs(atkts[sq]))
      end
  end; { BbdbWriteSqs }

  { ***** Hash routines ***** }

  procedure HashReset(var hash: hashtype); inline;
  begin
    with hash do
      begin
        bits0 := 0;
        bits1 := 0
      end
  end; { HashReset }

  procedure HashXor2D(var hash, hashop1: hashtype); inline;
  begin
    with hash do
      begin
        bits0 := bits0 xor hashop1.bits0;
        bits1 := bits1 xor hashop1.bits1
      end
  end; { HashXor2D }

  procedure HashRotateRight(var hash: hashtype);
    var
      bitflag: Boolean;
  begin
   with hash do
      begin
        bitflag := Odd(bits0);
        bits0 := bits0 div 2;
        if bitflag then
          bits0 := bits0 or (1 shl 63);
        bitflag := Odd(bits1);
        bits1 := bits1 div 2;
        if bitflag then
          bits1 := bits1 or (1 shl 63)
      end;
  end; { HashRotateRight }

  function HashEq(var op0, op1: hashtype): Boolean; inline;
  begin
    HashEq := (op0.bits0 = op1.bits0) and (op0.bits1 = op1.bits1)
  end; { HashEq }

  function HashCompare(var op0, op1: hashtype): rtrtype; inline;
    var
      myresult: rtrtype;
  begin
    if op0.bits1 < op1.bits1 then
      myresult := rtrlt
    else
      if op0.bits1 > op1.bits1 then
        myresult := rtrgt
      else
        if op0.bits0 < op1.bits0 then
          myresult := rtrlt
        else
          if op0.bits0 > op1.bits0 then
            myresult := rtrgt
          else
            myresult := rtreq;
    HashCompare := myresult
  end; { HashCompare }

  function HashEncode(var hash: hashtype): String;
    var
      myresult: String;
      index: Integer;
  begin
    with hash do
      begin
        myresult := '';
        for index := 0 to 15 do
          myresult := myresult + EncodeHexDigit((bits1 shr ((15 - index) * 4)) and 15);
        for index := 0 to 15 do
          myresult := myresult + EncodeHexDigit((bits0 shr ((15 - index) * 4)) and 15)
      end;
    HashEncode := myresult
  end; { HashEncode }

  { ***** Move cursor routines ***** }

  procedure McReset(var mc: mctype); inline;
  begin
    with mc do
      begin
        fmvn := startfmvn;
        good := startgood
      end
  end; { McReset }

  procedure McIncrement(var mc: mctype); inline;
  begin
    with mc do
      begin
        good := othercolor[good];
        if good = colorw then
          Inc(fmvn)
      end
  end; { McIncrement }

  procedure McDecrement(var mc: mctype); inline;
  begin
    with mc do
      begin
        good := othercolor[good];
        if good = colorb then
          Dec(fmvn)
      end
  end; { McDecrement }

  function McEncode(var mc: mctype): String;
    var
      myresult: String;
  begin
    with mc do
      begin
        myresult := EncodeInteger(fmvn);
        if good = colorb then
          myresult := myresult + '...'
      end;
    McEncode := myresult
  end; { McEncode }

  { ***** Move routines ***** }

  procedure MoveFlagSet(var move: movetype; mf: mftype); inline;
  begin
    with move do
      mfset := mfset + [mf]
  end; { MoveFlagSet }

  procedure MoveFlagReset(var move: movetype; mf: mftype); inline;
  begin
    with move do
      mfset := mfset - [mf]
  end; { MoveFlagReset }

  function MoveFlagTest(var move: movetype; mf: mftype): Boolean; inline;
  begin
    with move do
      MoveFlagTest := mf in mfset
  end; { MoveFlagTest }

  function MoveBestGain(var move: movetype): svtype;
  begin
    with move do
      MoveBestGain := mantosv[toman] + msctogain[msc]
  end; { MoveBestGain }

  procedure MoveSetCertain(var move: movetype; svvalue: svtype); inline;
  begin
    with move do
      begin
        MoveFlagSet(move, mfcert);
        sv := svvalue
      end
  end; { MoveSetCertain }

  procedure MoveSynthM1(var move: movetype; myfrsq, mytosq: sqtype; myfrman: mantype);
  begin
    with move do
      begin
        frsq := myfrsq;
        tosq := mytosq;
        frman := myfrman;
        toman := manvv;
        msc := mscreg;
        mfset := [];
        sv := svbroken
      end
  end; { MoveSynthM1 }

  procedure MoveSynthM2(var move: movetype; myfrsq, mytosq: sqtype; myfrman, mytoman: mantype);
  begin
    with move do
      begin
        frsq := myfrsq;
        tosq := mytosq;
        frman := myfrman;
        toman := mytoman;
        msc := mscreg;
        mfset := [];
        sv := svbroken
      end
  end; { MoveSynthM2 }

  procedure MoveSynthM3(
      var move: movetype; myfrsq, mytosq: sqtype; myfrman, mytoman: mantype; mymsc: msctype);
  begin
    with move do
      begin
        frsq := myfrsq;
        tosq := mytosq;
        frman := myfrman;
        toman := mytoman;
        msc := mymsc;
        mfset := [];
        sv := svbroken
      end
  end; { MoveSynthM3 }

  procedure MoveSynthM4(
      var move: movetype; myfrsq, mytosq: sqtype; myfrman: mantype; mymsc: msctype);
  begin
    with move do
      begin
        frsq := myfrsq;
        tosq := mytosq;
        frman := myfrman;
        toman := manvv;
        msc := mymsc;
        mfset := [];
        sv := svbroken
      end
  end; { MoveSynthM4 }

  function MoveIsSame(var move0, move1: movetype): Boolean; inline;
  begin
    MoveIsSame :=
        (move0.tosq = move1.tosq) and (move0.frsq = move1.frsq) and
        (move0.frman = move1.frman) and (move0.toman = move1.toman) and
        (move0.msc = move1.msc)
  end; { MoveIsSame }

  function MoveIsGainer(var move: movetype): Boolean; inline;
  begin
    with move do
      MoveIsGainer := (toman <> manvv) or (msc in gainmscset)
  end; { MoveIsGainer }

  function MoveIsHmvcReset(var move: movetype): Boolean; inline;
  begin
    with move do
      MoveIsHmvcReset := (frman in pawnmanset) or (toman <> manvv)
  end; { MoveIsHmvcReset }

  function MoveEncode(var move: movetype): santype;
    var
      myresult: santype;

    procedure AddCh(ch: Char);
    begin
      myresult := myresult + ch
    end; { AddCh }

    procedure AddStr(str: String);
    begin
      myresult := myresult + str
    end; { AddStr }

    procedure AddBfile(bfile: bfiletype);
    begin
      AddCh(bfiletochar[bfile])
    end; { AddBfile }

    procedure AddBrank(brank: branktype);
    begin
      AddCh(branktochar[brank])
    end; { AddBrank }

    procedure AddSq(sq: sqtype);
    begin
      AddBfile(sqtobfile[sq]);
      AddBrank(sqtobrank[sq])
    end; { AddSq }

    procedure AddPiece(piece: piecetype);
    begin
      AddCh(piecetochar[piece])
    end; { AddPiece }

  begin
    myresult := '';
    with move do
      begin
        if MoveFlagTest(move, mfnull) or MoveFlagTest(move, mfvoid) then
          if MoveFlagTest(move, mfnull) then
            AddStr('<null>')
          else
            AddStr('<void>')
        else
          begin
            case msc of
              mscreg:
                begin
                  if frman in pawnmanset then
                    begin
                      if toman <> manvv then
                        begin
                          AddBfile(sqtobfile[frsq]);
                          AddCh('x')
                        end
                    end
                  else
                    begin
                      AddPiece(mantopiece[frman]);
                      if MoveFlagTest(move, mfandf) then
                        AddBfile(sqtobfile[frsq]);
                      if MoveFlagTest(move, mfandr) then
                        AddBrank(sqtobrank[frsq]);
                      if toman <> manvv then
                        AddCh('x')
                    end;
                  AddSq(tosq)
                end;
              mscepc:
                begin
                  AddBfile(sqtobfile[frsq]);
                  AddCh('x');
                  AddSq(tosq)
                end;
              msccqs:
                AddStr('O-O-O');
              msccks:
                AddStr('O-O');
              mscppn, mscppb, mscppr, mscppq:
                begin
                  if toman <> manvv then
                    begin
                      AddBfile(sqtobfile[frsq]);
                      AddCh('x')
                    end;
                  AddSq(tosq);
                  AddCh('=');
                  AddPiece(msctopiece[msc])
                end
            end; { case }
            if MoveFlagTest(move, mfchck) then
              if MoveFlagTest(move, mfchmt) then
                AddCh('#')
              else
                AddCh('+')
          end
      end;
    MoveEncode := myresult
  end; { MoveEncode }

  function MoveEncodeMc(var move: movetype; var mc: mctype): String;
  begin
    MoveEncodeMc := McEncode(mc) + ' ' + MoveEncode(move)
  end; { MoveEncodeMc }

  function MoveEncodeFlags(var move: movetype): String;
    var
      myresult: String;
      needspace: Boolean;
      mf: mftype;
  begin
    myresult := '[';
    needspace := False;
    for mf := mfmin to mfmax do
      if MoveFlagTest(move, mf) then
        begin
          if needspace then
            myresult := myresult + ' '
          else
            needspace := True;
          myresult := myresult + mfnames[mf]
        end;
    myresult := myresult + ']';
    MoveEncodeFlags := myresult
  end; { MoveEncodeFlags }

  { ***** Move node routines ***** }

  function MnListDetachHead(var mnlist: mnlisttype): mnptrtype; inline;
    var
      myresult: mnptrtype;
  begin
    with mnlist do
      begin
        myresult := head;
        head := head^.next;
        if head = nil then
          tail := nil
        else
          head^.prev := nil;
        Dec(ecount)
      end;
    MnListDetachHead := myresult
  end; { MnListDetachHead }

  procedure MnListAppendTail(var mnlist: mnlisttype; mnptr: mnptrtype); inline;
  begin
    with mnlist, mnptr^ do
      begin
        prev := tail;
        next := nil;
        if tail = nil then
          head := mnptr
        else
          tail^.next := mnptr;
        tail := mnptr;
        Inc(ecount)
      end
  end; { MnListAppendTail }

  function MnListDetachTail(var mnlist: mnlisttype): mnptrtype; inline;
    var
      myresult: mnptrtype;
  begin
    with mnlist do
      begin
        myresult := tail;
        tail := tail^.prev;
        if tail = nil then
          head := nil
        else
          tail^.next := nil;
        Dec(ecount)
      end;
    MnListDetachTail := myresult
  end; { MnListDetachTail }

  procedure MnListReset(var mnlist: mnlisttype);
    var
      mnptr: mnptrtype;
  begin
    with mnlist do
      while tail <> nil do
        begin
          mnptr := MnListDetachTail(mnlist);
          Dispose(mnptr)
        end
  end; { MnListReset }

  procedure MnListInit(var mnlist: mnlisttype);
  begin
    with mnlist do
      begin
        ecount := 0;
        head := nil;
        tail := nil
      end
  end; { MnListInit }

  procedure MnListTerm(var mnlist: mnlisttype);
  begin
    MnListReset(mnlist)
  end; { MnListTerm }

  { ***** Perft transposition entry signature routines ***** }

  procedure TtprftsigReset(var ttprftsig: ttprftsigtype);
  begin
    with ttprftsig do
      begin
        sigword0 := 0;
        sigword1 := 0
      end
  end;

  function TtprftsigEq(var ttprftsig0, ttprftsig1: ttprftsigtype): Boolean;
  begin
    TtprftsigEq :=
      (ttprftsig0.sigword0 = ttprftsig1.sigword0) and (ttprftsig0.sigword1 = ttprftsig0.sigword1)
  end;

  { ***** Generation move set routines ***** }

  procedure GmsReset(var gms: gmstype); inline;
  begin
    with gms do
      movecount := 0
  end; { GmsReset }

  procedure GmsPush(var gms: gmstype; var move: movetype); inline;
  begin
    with gms do
      begin
        moves[movecount] := move;
        Inc(movecount)
      end
  end; { GmsPush }

  procedure GmsPushM1(var gms: gmstype; myfrsq, mytosq: sqtype; myfrman: mantype); inline;
  begin
    with gms do
      begin
        with moves[movecount] do
          begin
            frsq := myfrsq;
            tosq := mytosq;
            frman := myfrman;
            toman := manvv;
            msc := mscreg;
            mfset := [];
            sv := svbroken
          end;
        Inc(movecount)
      end
  end; { GmsPushM1 }

  procedure GmsPushM2(
      var gms: gmstype; myfrsq, mytosq: sqtype; myfrman, mytoman: mantype); inline;
  begin
    with gms do
      begin
        with moves[movecount] do
          begin
            frsq := myfrsq;
            tosq := mytosq;
            frman := myfrman;
            toman := mytoman;
            msc := mscreg;
            mfset := [];
            sv := svbroken
          end;
        Inc(movecount)
      end
  end; { GmsPushM2 }

  procedure GmsPushM3(
      var gms: gmstype; myfrsq, mytosq: sqtype; myfrman, mytoman: mantype; mymsc: msctype); inline;
  begin
    with gms do
      begin
        with moves[movecount] do
          begin
            frsq := myfrsq;
            tosq := mytosq;
            frman := myfrman;
            toman := mytoman;
            msc := mymsc;
            mfset := [];
            sv := svbroken
          end;
        Inc(movecount)
      end
  end; { GmsPushM3 }

  procedure GmsPushM4(
      var gms: gmstype; myfrsq, mytosq: sqtype; myfrman: mantype; mymsc: msctype); inline;
  begin
    with gms do
      begin
        with moves[movecount] do
          begin
            frsq := myfrsq;
            tosq := mytosq;
            frman := myfrman;
            toman := manvv;
            msc := mymsc;
            mfset := [];
            sv := svbroken
          end;
        Inc(movecount)
      end
  end; { GmsPushM4 }

  procedure GmsPushPsCapt(
      var gms: gmstype; myfrsq, mytosq: sqtype; myfrman, mytoman: mantype); inline;
    var
      msc: msctype;
  begin
    for msc := mscppq downto mscppn do
      GmsPushM3(gms, myfrsq, mytosq, myfrman, mytoman, msc)
  end; { GmsPushPsCapt }

  procedure GmsPushPsHold(var gms: gmstype; myfrsq, mytosq: sqtype; myfrman: mantype); inline;
    var
      msc: msctype;
  begin
    for msc := mscppq downto mscppn do
      GmsPushM4(gms, myfrsq, mytosq, myfrman, msc)
  end; { GmsPushPsHold }

  function GmsLocateMove(var gms: gmstype; var move: movetype): Integer;
    var
      myresult, index: Integer;
  begin
    myresult := -1;
    index := 0;
    with gms do
      while (myresult < 0) and (index < movecount) do
        if MoveIsSame(move, moves[index]) then
          myresult := index
        else
          Inc(index);
    GmsLocateMove := myresult
  end; { GmsLocateMove }

  function GmsLocateMoveNoFail(var gms: gmstype; var move: movetype): Integer;
    var
      myresult: Integer;
  begin
    myresult := GmsLocateMove(gms, move);
    if myresult < 0 then
      WTF('GmsLocateMoveNoFail: move not found');
    GmsLocateMoveNoFail := myresult
  end; { GmsLocateMoveNoFail }

  function GmsBestUnsearchedIndex(var gms: gmstype): Integer;
    var
      myresult, index: Integer;
      bestsv: svtype;
  begin
    with gms do
      begin
        myresult := -1;
        bestsv := svbroken;
        for index := 0 to movecount - 1 do
          if not MoveFlagTest(moves[index], mfsrch) then
            if myresult < 0 then
              begin
                bestsv := moves[index].sv;
                myresult := index
              end
            else
              if moves[index].sv > bestsv then
                begin
                  bestsv := moves[index].sv;
                  myresult := index
                end
      end;
    GmsBestUnsearchedIndex := myresult
  end; { GmsBestUnsearchedIndex }

  function GmsFirstUnsearchedIndex(var gms: gmstype): Integer;
    var
      myresult, index: Integer;
  begin
    with gms do
      begin
        myresult := -1;
        index := 0;
        while (myresult < 0) and (index < movecount) do
          if not MoveFlagTest(moves[index], mfsrch) then
            myresult := index
          else
            Inc(index)
      end;
    GmsFirstUnsearchedIndex := myresult
  end; { GmsFirstUnsearchedIndex }

  procedure GmsMoveToFront(var gms: gmstype; var move: movetype);
    var
      index, moveindex: Integer;
      tempmove: movetype;
  begin
    with gms do
      begin
        moveindex := GmsLocateMoveNoFail(gms, move);
        if moveindex <> 0 then
          begin
            tempmove := moves[moveindex];
            for index := genmin to moveindex - 1 do
              moves[moveindex - index] := moves[moveindex - index - 1];
            moves[0] := tempmove
          end
      end
  end; { GmsMoveToFront }

  procedure GmsLoadFromGms(var gms, altgms: gmstype);
    var
      index: Integer;
  begin
    GmsReset(gms);
    for index := genmin to altgms.movecount - 1 do
      GmsPush(gms, altgms.moves[index])
  end; { GmsLoadFromGms }

  procedure GmsSortBySan(var gms: gmstype);
    var
      index: Integer;
      tempmoves: array [gentype] of movetype;
      altindex, saveindex: array [gentype] of gentype;
      altsan, savesan: array [gentype] of santype;

    procedure SortSanSegment(start: gentype; count: Integer);
      var
        start0, start1: gentype;
        count0, count1: Integer;
        tempindex: gentype;
        tempsan: santype;
        fill: Integer;
        pick0, pick1: Integer;
        pick0limit, pick1limit: Integer;
    begin
      if count > 1 then
        begin

          { At least two records need sorted }

          if count = 2 then
            begin

              { Sort two records }

              if altsan[start] > altsan[start + 1] then
                begin

                  { Simple exchange }

                  tempindex := altindex[start];
                  altindex[start] := altindex[start + 1];
                  altindex[start + 1] := tempindex;
                  tempsan := altsan[start];
                  altsan[start] := altsan[start + 1];
                  altsan[start + 1] := tempsan
                end
            end
          else
            begin

              { Sort more than two records; start with split calculation }

              count0 := count div 2;
              count1 := count - count0;
              start0 := start;
              start1 := start0 + count0;

              { Sort the two segments }

              SortSanSegment(start0, count0);
              SortSanSegment(start1, count1);

              { Set up to merge the results of two segments }

              fill := start;
              pick0 := start0;
              pick1 := start1;
              pick0limit := pick0 + count0;
              pick1limit := pick1 + count1;

              { Fill while at least one unpicked record in each segment }

              while (pick0 < pick0limit) and (pick1 < pick1limit) do
                begin
                  if altsan[pick0] < altsan[pick1] then
                    begin
                      savesan[fill] := altsan[pick0];
                      saveindex[fill] := altindex[pick0];
                      Inc(pick0)
                    end
                  else
                    begin
                      savesan[fill] := altsan[pick1];
                      saveindex[fill] := altindex[pick1];
                      Inc(pick1)
                    end;
                  Inc(fill)
                end;

              { Add any remaining records from the first segment }

              while pick0 < pick0limit do
                begin
                  savesan[fill] := altsan[pick0];
                  saveindex[fill] := altindex[pick0];
                  Inc(pick0);
                  Inc(fill)
                end;

              { Add any remaining records from the second segment }

              while pick1 < pick1limit do
                begin
                  savesan[fill] := altsan[pick1];
                  saveindex[fill] := altindex[pick1];
                  Inc(pick1);
                  Inc(fill)
                end;

              { Copy to result }

              for fill := start to (start + count - 1) do
                begin
                  altsan[fill] := savesan[fill];
                  altindex[fill] := saveindex[fill]
                end
            end
        end
    end; { SortSanSegment }

  begin
    with gms do
      if movecount > 1 then
        begin
          for index := 0 to movecount - 1 do
            begin
              tempmoves[index] := moves[index];
              altindex[index] := index;
              altsan[index] := MoveEncode(moves[index])
            end;
          SortSanSegment(0, movecount);
          for index := 0 to movecount - 1 do
            moves[index] := tempmoves[altindex[index]]
        end
  end; { GmsSortBySan }

  procedure GmsSortByScore(var gms: gmstype);
    var
      index: Integer;
      tempmoves: array [gentype] of movetype;
      altindex, saveindex: array [gentype] of gentype;
      altsv, savesv: array [gentype] of svtype;

    procedure SortScoreSegment(start: gentype; count: Integer);
      var
        start0, start1: gentype;
        count0, count1: Integer;
        tempindex: gentype;
        tempsv: svtype;
        fill: Integer;
        pick0, pick1: Integer;
        pick0limit, pick1limit: Integer;
    begin
      if count > 1 then
        begin

          { At least two records need sorted }

          if count = 2 then
            begin

              { Sort two records }

              if altsv[start] < altsv[start + 1] then
                begin

                  { Simple exchange }

                  tempindex := altindex[start];
                  altindex[start] := altindex[start + 1];
                  altindex[start + 1] := tempindex;
                  tempsv := altsv[start];
                  altsv[start] := altsv[start + 1];
                  altsv[start + 1] := tempsv
                end
            end
          else
            begin

              { Sort more than two records; start with split calculation }

              count0 := count div 2;
              count1 := count - count0;
              start0 := start;
              start1 := start0 + count0;

              { Sort the two segments }

              SortScoreSegment(start0, count0);
              SortScoreSegment(start1, count1);

              { Set up to merge the results of two segments }

              fill := start;
              pick0 := start0;
              pick1 := start1;
              pick0limit := pick0 + count0;
              pick1limit := pick1 + count1;

              { Fill while at least one unpicked record in each segment }

              while (pick0 < pick0limit) and (pick1 < pick1limit) do
                begin
                  if altsv[pick0] > altsv[pick1] then
                    begin
                      savesv[fill] := altsv[pick0];
                      saveindex[fill] := altindex[pick0];
                      Inc(pick0)
                    end
                  else
                    begin
                      savesv[fill] := altsv[pick1];
                      saveindex[fill] := altindex[pick1];
                      Inc(pick1)
                    end;
                  Inc(fill)
                end;

              { Add any remaining records from the first segment }

              while pick0 < pick0limit do
                begin
                  savesv[fill] := altsv[pick0];
                  saveindex[fill] := altindex[pick0];
                  Inc(pick0);
                  Inc(fill)
                end;

              { Add any remaining records from the second segment }

              while pick1 < pick1limit do
                begin
                  savesv[fill] := altsv[pick1];
                  saveindex[fill] := altindex[pick1];
                  Inc(pick1);
                  Inc(fill)
                end;

              { Copy to result }

              for fill := start to (start + count - 1) do
                begin
                  altsv[fill] := savesv[fill];
                  altindex[fill] := saveindex[fill]
                end
            end
        end
    end; { SortScoreSegment }

  begin
    with gms do
      if movecount > 1 then
        begin
          for index := 0 to movecount - 1 do
            begin
              tempmoves[index] := moves[index];
              altindex[index] := index;
              altsv[index] := moves[index].sv
            end;
          SortScoreSegment(0, movecount);
          for index := 0 to movecount - 1 do
            moves[index] := tempmoves[altindex[index]]
        end
  end; { GmsSortByScore }

  procedure GmsMoveChecksToFront(var gms: gmstype);
    var
      auxgms: gmstype;
      index, limit: Integer;
  begin
    with gms do
      begin
        GmsReset(auxgms);
        limit := movecount;
        for index := genmin to limit - 1 do
          GmsPush(auxgms, moves[index]);
        GmsReset(gms);
        for index := genmin to limit - 1 do
          if MoveFlagTest(auxgms.moves[index], mfchck) then
            GmsPush(gms, auxgms.moves[index]);
        for index := genmin to limit - 1 do
          if not MoveFlagTest(auxgms.moves[index], mfchck) then
            GmsPush(gms, auxgms.moves[index])
      end
  end; { GmsMoveChecksToFront }

  function GmsBestCertainScore(var gms: gmstype): svtype;
    var
      myresult: svtype;
      index: Integer;
  begin
    with gms do
      begin
        myresult := svbroken;
        index := genmin;
        while index < movecount do
          begin
            if MoveFlagTest(moves[index], mfcert) and (moves[index].sv > myresult) then
              myresult := moves[index].sv;
            Inc(index)
          end
      end;
    GmsBestCertainScore := myresult
  end; { GmsBestCertainScore }

  function GmsIndexFirstMatchCertainScore(var gms: gmstype; sv: svtype): Integer;
    var
      index: Integer;
      match: Integer;
  begin
    with gms do
      begin
        match := -1;
        index := genmin;
        while (match < 0) and (index < movecount) do
          begin
            if MoveFlagTest(moves[index], mfcert) and (moves[index].sv = sv) then
              match := index
            else
              Inc(index)
          end
      end;
    GmsIndexFirstMatchCertainScore := match
  end; { GmsIndexFirstMatchCertainScore }

  function GmsIndexFirstUncertain(var gms: gmstype): Integer;
    var
      index: Integer;
      match: Integer;
  begin
    with gms do
      begin
        match := -1;
        index := genmin;
        while (match < 0) and (index < movecount) do
          begin
            if not MoveFlagTest(moves[index], mfcert) then
              match := index
            else
              Inc(index)
          end
      end;
    GmsIndexFirstUncertain := match
  end; { GmsIndexFirstUncertain }

  function GmsCountCertain(var gms: gmstype): Integer;
    var
      myresult: Integer;
      index: Integer;
  begin
    with gms do
      begin
        myresult := 0;
        for index := 0 to movecount - 1 do
          if MoveFlagTest(moves[index], mfcert) then
            Inc(myresult)
      end;
    GmsCountCertain := myresult
  end; { GmsCountCertain }

  function GmsEncode(var gms: gmstype): String;
    var
      myresult: String;
      index: Integer;
  begin
    with gms do
      begin
        myresult := '';
        for index := 0 to movecount - 1 do
          begin
            if index > 0 then
              myresult := myresult + ' ';
            myresult := myresult + MoveEncode(moves[index])
          end
      end;
    GmsEncode := myresult
  end; { GmsEncode }

  { ***** Spev routines ***** }

  procedure SpevListAppendTail(var spevlist: spevlisttype; spevptr: spevptrtype); inline;
  begin
    with spevlist, spevptr^ do
      begin
        prev := tail;
        next := nil;
        if tail = nil then
          head := spevptr
        else
          tail^.next := spevptr;
        tail := spevptr;
        Inc(ecount)
      end
  end; { SpevListAppendTail }

  function SpevListDetachTail(var spevlist: spevlisttype): spevptrtype; inline;
    var
      myresult: spevptrtype;
  begin
    with spevlist do
      begin
        myresult := tail;
        tail := tail^.prev;
        if tail = nil then
          head := nil
        else
          tail^.next := nil;
        Dec(ecount)
      end;
    SpevListDetachTail := myresult
  end; { SpevListDetachTail }

  procedure SpevListReset(var spevlist: spevlisttype);
    var
      spevptr: spevptrtype;
  begin
    with spevlist do
      while tail <> nil do
        begin
          spevptr := SpevListDetachTail(spevlist);
          Dispose(spevptr)
        end
  end; { SpevListReset }

  procedure SpevListInit(var spevlist: spevlisttype);
  begin
    with spevlist do
      begin
        ecount := 0;
        head := nil;
        tail := nil
      end
  end; { SpevListInit }

  procedure SpevListTerm(var spevlist: spevlisttype);
  begin
    SpevListReset(spevlist)
  end; { SpevListTerm }

  { ***** Position routines ***** }

  function PosEncode(var pos: postype): fentype; forward;

  procedure PosClear(var pos: postype);
    var
      color: colorrtype;
  begin
    with pos do
      begin
        BoardReset(board);
        good := startgood;
        evil := startevil;
        cavs := [];
        epsq := sqnil;
        hmvc := starthmvc;
        fmvn := startfmvn;
        BbdbReset(bbdb);
        msig := 0;
        wood := 0;
        CensusReset(census);
        for color := colorrmin to colorrmax do
          begin
            matv[color] := 0;
            ksqv[color] := sqnil
          end;
        inch := False;
        dbch := False;
        BbReset(pmbb);
        BbReset(fmbb);
        HashReset(mphc);
        HashReset(pshc);
        ifen := PosEncode(pos)
      end
  end; { PosClear }

  procedure PosInit(var pos: postype);
  begin
    with pos do
      begin
        PosClear(pos);
        SpevListInit(freespevlist);
        SpevListInit(usedspevlist)
      end
  end; { PosInit }

  procedure PosTerm(var pos: postype);
  begin
    with pos do
      begin
        SpevListTerm(freespevlist);
        SpevListTerm(usedspevlist)
      end
  end; { PosTerm }

  procedure PosCalcGameHash(var pos: postype; var hash: hashtype);
    var
      spevptr: spevptrtype;
  begin
    with pos do
      begin
        HashReset(hash);
        spevptr := usedspevlist.head;
        while spevptr <> nil do
          begin
            HashRotateRight(hash);
            HashXor2D(hash, spevptr^.spevmphc);
            spevptr := spevptr^.next
          end;
        HashRotateRight(hash);
        HashXor2D(hash, mphc)
      end
  end; { PosCalcGameHash }

  procedure PosLoadToMc(var pos: postype; var mc: mctype);
  begin
    with pos do
      begin
        mc.fmvn := fmvn;
        mc.good := good
      end
  end; { PosLoadToMc }

  procedure PosAddMan(var pos: postype; man: manrtype; sq: sqtype);
    var
      color: colorrtype;
  begin

    { Square must be vacant }

    with pos, board, census do
      begin
        color := mantocolor[man];
        sqv[sq] := man;
        Inc(msig, msigdeltavec[man]);
        Inc(matv[color], mantosv[man]);
        Inc(wood);
        Inc(cic[color]);
        Inc(mic[man]);
        if man in kingmanset then
          ksqv[color] := sq;
        HashXor2D(mphc, hashmansqvec[man, sq]);
        if man in pawnmanset then
          HashXor2D(pshc, hashmansqvec[man, sq]);
        BbdbAddMan(bbdb, man, sq)
      end

  end; { PosAddMan }

  procedure PosDelMan(var pos: postype; sq: sqtype);
    var
      man: manrtype;
      color: colorrtype;
  begin

    { Square must be occupied }

    with pos, board, census do
      begin
        man := sqv[sq];
        color := mantocolor[man];
        sqv[sq] := manvv;
        Dec(msig, msigdeltavec[man]);
        Dec(matv[color], mantosv[man]);
        Dec(wood);
        Dec(cic[color]);
        Dec(mic[man]);
        if man in kingmanset then
          ksqv[color] := sqnil;
        HashXor2D(mphc, hashmansqvec[man, sq]);
        if man in pawnmanset then
          HashXor2D(pshc, hashmansqvec[man, sq]);
        BbdbDelMan(bbdb, man, sq)
      end

  end; { PosDelMan }

  procedure PosMovMan(var pos: postype; frsq, tosq: sqtype);
    var
      man: manrtype;
      color: colorrtype;
  begin

    { First square must be occupied; second square must be vacant }

    with pos, board do
      begin
        man := sqv[frsq];
        color := mantocolor[man];
        sqv[frsq] := manvv;
        sqv[tosq] := man;
        if man in kingmanset then
          ksqv[color] := tosq;
        HashXor2D(mphc, hashmansqvec[man, frsq]);
        HashXor2D(mphc, hashmansqvec[man, tosq]);
        if man in pawnmanset then
          begin
            HashXor2D(pshc, hashmansqvec[man, frsq]);
            HashXor2D(pshc, hashmansqvec[man, tosq])
          end;
        BbdbMovMan(bbdb, man, frsq, tosq)
      end

  end; { PosMovMan }

  procedure PosCaptureMan(var pos: postype; frsq, tosq: sqtype);
    var
     frman, toman: manrtype;
     frcolor, tocolor: colorrtype;
  begin
    with pos, board, census do
     begin

        frman := sqv[frsq];
        toman := sqv[tosq];
        frcolor := mantocolor[frman];
        tocolor := mantocolor[toman];
        sqv[frsq] := manvv;
        sqv[tosq] := frman;

        Dec(msig, msigdeltavec[toman]);
        Dec(matv[tocolor], mantosv[toman]);
        Dec(wood);
        Dec(cic[tocolor]);
        Dec(mic[toman]);
        if toman in kingmanset then
          ksqv[tocolor] := sqnil;
        HashXor2D(mphc, hashmansqvec[toman, tosq]);
        if toman in pawnmanset then
          HashXor2D(pshc, hashmansqvec[toman, tosq]);

        if frman in kingmanset then
          ksqv[frcolor] := tosq;
        HashXor2D(mphc, hashmansqvec[frman, frsq]);
        HashXor2D(mphc, hashmansqvec[frman, tosq]);
        if frman in pawnmanset then
          begin
            HashXor2D(pshc, hashmansqvec[frman, frsq]);
            HashXor2D(pshc, hashmansqvec[frman, tosq])
          end;

        BbdbCaptureMan(bbdb, frman, toman, frsq, tosq)

      end
  end; { PosCaptureMan }

  procedure PosRevCaptMan(var pos: postype; toman: manrtype; frsq, tosq: sqtype);
    var
     frman: manrtype;
     frcolor, tocolor: colorrtype;
  begin
    with pos, board, census do
     begin

        frman := sqv[tosq];
        frcolor := mantocolor[frman];
        tocolor := mantocolor[toman];
        sqv[frsq] := frman;
        sqv[tosq] := toman;

        if frman in kingmanset then
          ksqv[frcolor] := frsq;
        HashXor2D(mphc, hashmansqvec[frman, frsq]);
        HashXor2D(mphc, hashmansqvec[frman, tosq]);
        if frman in pawnmanset then
          begin
            HashXor2D(pshc, hashmansqvec[frman, frsq]);
            HashXor2D(pshc, hashmansqvec[frman, tosq])
          end;

        Inc(msig, msigdeltavec[toman]);
        Inc(matv[tocolor], mantosv[toman]);
        Inc(wood);
        Inc(cic[tocolor]);
        Inc(mic[toman]);
        if toman in kingmanset then
          ksqv[tocolor] := tosq;
        HashXor2D(mphc, hashmansqvec[toman, tosq]);
        if toman in pawnmanset then
          HashXor2D(pshc, hashmansqvec[toman, tosq]);

        BbdbRevCaptMan(bbdb, frman, toman, frsq, tosq)

     end
  end; { PosRevCaptMan }

  procedure PosRebuild(var pos: postype);

    procedure PosRebuildCheckStatuses;
      var
        goodkingsq: sqxtype;
        atkbb: bbtype;
    begin
      with pos, bbdb do
        begin
          goodkingsq := ksqv[good];
          inch := BbTestSq(atkbc[evil], goodkingsq);
          if inch then
            begin
              BbAnd2(atkbb, locbc[evil], atkts[goodkingsq]);
              dbch := BbCount(atkbb) > 1
            end
          else
            dbch := False
        end
    end; { PosRebuildCheckStatuses }

    procedure PosRebuildPinBitboards;
      var
        color0, color1: colortype;
        king0sq: sqxtype;
        sweep1bb: bbtype;
        cand0bb: bbtype;
        cand0sq: sqxtype;
        dir: dirtype;
        deltar: Integer;
    begin
      with pos, bbdb do
        begin

          { Initialize the pinned man bitboard and frozen man bitboard results }

          BbReset(pmbb);
          BbReset(fmbb);

          { Loop through each color to locate pinned men }

          for color0 := colorrmin to colorrmax do
            begin

              { Get the king square of the first color }

              king0sq := ksqv[color0];

              { Get the second color and check if there are any second color sweep men }

              color1 := othercolor[color0];
              BbAnd2(sweep1bb, sweep, locbc[color1]);
              if not BbIsReset(sweep1bb) then
                begin

                  { Build a bitboard of candidate pinned men for the first color }

                  BbAnd3(cand0bb, locbc[color0], sweepraybbvec[king0sq], atkbc[color1]);

                  { Loop through each first color candidate }

                  repeat
                    cand0sq := BbNextSq(cand0bb);
                    if cand0sq <> sqnil then

                      { Check for no men between the king and the candidate }

                      if BbNI2(merge, pathwaybbvec[king0sq, cand0sq]) then
                        begin

                          { Calculate the king/candidate direction and check if a real pin exists }

                          dir := compass[king0sq, cand0sq];
                          if not BbNI3(openraybbvec[cand0sq, dir], sweep1bb, atkts[cand0sq]) then
                            begin

                              { Pinned man found; add to pinned man result and check frozen status }

                              BbSetSq(pmbb, cand0sq);
                              case mantopiece[board.sqv[cand0sq]] of
                                piecep:
                                  begin
                                    deltar := CalcBrankDelta(king0sq, cand0sq);
                                    if dir in orthodirset then
                                      begin
                                        if deltar = 0 then
                                          BbSetSq(fmbb, cand0sq)
                                      end
                                    else
                                      begin
                                        if color0 = colorw then
                                          begin
                                            if deltar < 0 then
                                              BbSetSq(fmbb, cand0sq)
                                          end
                                        else
                                          begin
                                            if deltar > 0 then
                                              BbSetSq(fmbb, cand0sq)
                                          end
                                      end
                                  end;
                                piecen:
                                  BbSetSq(fmbb, cand0sq);
                                pieceb:
                                  if dir in orthodirset then
                                    BbSetSq(fmbb, cand0sq);
                                piecer:
                                  if dir in diagodirset then
                                    BbSetSq(fmbb, cand0sq);
                                pieceq:
                              end { case }
                            end
                        end
                  until cand0sq = sqnil
                end
            end
        end
    end; { PosRebuildPinBitboards }

  begin
    PosRebuildCheckStatuses;
    PosRebuildPinBitboards
  end; { PosRebuild }

  procedure PosBuildRunway(var pos: postype; var runway: runwaytype);
    var
      evilkingsq: sqtype;
      dir: dirtype;
      scansq: sqxtype;
      scanindex: Integer;
      color: colortype;
      goodsweepbb: bbtype;
      scanbb: bbtype;
  begin
    with pos, board, bbdb, runway do
      begin
        BbReset(disbb);
        evilkingsq := ksqv[evil];
        BbAnd2(goodsweepbb, sweep, locbc[good]);

        { Pawn runway }

        prwbb := pawnatkbbvec[evil, evilkingsq];

        { Knight runway }

        nrwbb := knightatkbbvec[evilkingsq];

        { Bishop runway }

        BbReset(brwbb);
        for dir := diagodirmin to diagodirmax do
          begin
            scanindex := scanmap[evilkingsq, dir];
            scansq := scansqs[scanindex];
            while scansq <> sqnil do
              begin
                color := mantocolor[sqv[scansq]];
                if color = colorv then
                  begin
                    BBSetSq(brwbb, scansq);
                    Inc(scanindex);
                    scansq := scansqs[scanindex]
                  end
                else
                  begin
                    if color = evil then
                      BBSetSq(brwbb, scansq)
                    else
                      BBSetSq(disbb, scansq);
                    scansq := sqnil
                  end
              end
          end;

        { Rook runway }

        BbReset(rrwbb);
        for dir := orthodirmin to orthodirmax do
          begin
            scanindex := scanmap[evilkingsq, dir];
            scansq := scansqs[scanindex];
            while scansq <> sqnil do
              begin
                color := mantocolor[sqv[scansq]];
                if color = colorv then
                  begin
                    BBSetSq(rrwbb, scansq);
                    Inc(scanindex);
                    scansq := scansqs[scanindex]
                  end
                else
                  begin
                    if color = evil then
                      BBSetSq(rrwbb, scansq)
                    else
                      BBSetSq(disbb, scansq);
                    scansq := sqnil
                  end
              end
          end;

        { Queen runway }

        BbIor2(qrwbb, brwbb, rrwbb);

        { Discovery runway, second pass }

        scanbb := disbb;
        repeat
          scansq := BbNextSq(scanbb);
          if scansq <> sqnil then
            if BbNI3(goodsweepbb, beambbvec[evilkingsq, scansq], atkts[scansq]) then
              BbResetSq(disbb, scansq)
        until scansq = sqnil

      end
  end; { PosBuildRunway }

  function PosIsCastlingLegal(var pos: postype; cast: casttype): Boolean;
    var
      myresult: Boolean;
  begin
    with pos, bbdb, cdrvec[cast] do
      if karc <> good then
        myresult := False
      else
        if not (cast in cavs) then
          myresult := False
        else
          if not BbNI2(merge, cvbb) then
            myresult := False
          else
            myresult := BbNI2(atkbc[evil], cabb);
    PosIsCastlingLegal := myresult
  end; { PosIsCastlingLegal }

  function PosIsCastlingChecking(var pos: postype; cast: casttype): Boolean;
    var
      myresult: Boolean;
  begin
    myresult := PosIsCastlingLegal(pos, cast);
    if myresult then
      with pos, bbdb, cdrvec[cast] do
        begin
          BbdbMovMan(bbdb, kman, k0sq, k1sq);
          BbdbMovMan(bbdb, rman, r0sq, r1sq);
          if not BbTestSq(atkbc[good], ksqv[evil]) then
            myresult := False;
          BbdbMovMan(bbdb, rman, r1sq, r0sq);
          BbdbMovMan(bbdb, kman, k1sq, k0sq);
        end;
    PosIsCastlingChecking := myresult
  end; { PosIsCastlingChecking }

  function PosIsEnPassantMoveLegal(var pos: postype; var move: movetype): Boolean;
    var
      myresult: Boolean;
      vmsq: sqtype;
      evilpawn: manrtype;
  begin
    with pos, move, bbdb do
      begin
        vmsq := advance[tosq, pawnadvdir[evil]];
        evilpawn := synthpawn[evil];
        BbdbDelMan(bbdb, evilpawn, vmsq);
        BbdbMovMan(bbdb, frman, frsq, tosq);
        myresult := not BbTestSq(atkbc[evil], ksqv[good]);
        BbdbMovMan(bbdb, frman, tosq, frsq);
        BbdbAddMan(bbdb, evilpawn, vmsq)
      end;
    PosIsEnPassantMoveLegal := myresult
  end; { PosIsEnPassantMoveLegal }

  function PosIsEnPassantMoveChecking(var pos: postype; var move: movetype): Boolean;
    var
      myresult: Boolean;
      vmsq: sqtype;
      evilpawn: manrtype;
  begin
    with pos, move, bbdb do
      begin
        vmsq := advance[tosq, pawnadvdir[evil]];
        evilpawn := synthpawn[evil];
        BbdbDelMan(bbdb, evilpawn, vmsq);
        BbdbMovMan(bbdb, frman, frsq, tosq);
        myresult := not BbTestSq(atkbc[evil], ksqv[good]) and BbTestSq(atkbc[good], ksqv[evil]);
        BbdbMovMan(bbdb, frman, tosq, frsq);
        BbdbAddMan(bbdb, evilpawn, vmsq)
      end;
    PosIsEnPassantMoveChecking := myresult
  end; { PosIsEnPassantMoveChecking }

  procedure PosGenerate(var pos: postype; var gms: gmstype);

    procedure PosGenerateEvasion;
      var
        goodkingsq: sqtype;
        goodpawn, goodking: manrtype;
        goodbb, goodpawnbb: bbtype;
        r2brank, r4brank, r8brank: branktype;
        advdir: dirtype;
        singlecheck: Boolean;
        checkerbb: bbtype;
        checkersq: sqxtype;
        checkerman: mantype;
        checkeropr: Boolean;
        flightbb: bbtype;
        flightsq: sqxtype;
        atkbb: bbtype;
        atksq: sqxtype;
        defbb: bbtype;
        defsq: sqxtype;
        defman: manrtype;
        shadowsq: sqxtype;
        cvpwbb: bbtype;
        pathbb: bbtype;
        pathsq: sqxtype;
        ipdbb: bbtype;
        ipdsq: sqxtype;
        epmove: movetype;
    begin
      with pos, board, bbdb do
        begin

          { Set various local constant values }

          goodkingsq := ksqv[good];
          goodpawn := synthpawn[good];
          goodking := synthking[good];
          goodbb := locbc[good];
          goodpawnbb := locbm[goodpawn];
          r2brank := normalbrank[good, brank2];
          r4brank := normalbrank[good, brank4];
          r8brank := normalbrank[good, brank8];
          advdir := pawnadvdir[good];
          singlecheck := not dbch;
          BbAnd2(checkerbb, locbc[evil], atkts[goodkingsq]);

          { Set various checker data local constant values according to double check status }

          if singlecheck then
            begin
              checkersq := BbFirstSq(checkerbb);
              checkerman := sqv[checkersq];
              checkeropr := sqtobrank[checkersq] = r8brank
            end
          else
            begin
              checkersq := sqnil;
              checkerman := manvv;
              checkeropr := False
            end;

          { Initialize the king flight squares bitboard }

          flightbb := kingatkbbvec[goodkingsq];
          BbAnd2C2D(flightbb, goodbb);
          BbAnd2C2D(flightbb, atkbc[evil]);

          { Remove any shadow squares from the flight bitboard }

          atkbb := checkerbb;
          repeat
            atksq := BbNextSq(atkbb);
            if atksq <> sqnil then
              if BbTestSq(sweep, atksq) then
                begin
                  shadowsq := shadows[atksq, goodkingsq];
                  if shadowsq <> sqnil then
                    BbResetSq(flightbb, shadowsq)
                end
          until atksq = sqnil;

          { Attempt capture of a singleton attacker (no king moves, no en passant) }

          if singlecheck then
            begin
              BbAnd2(defbb, atkts[checkersq], goodbb);
              BbAnd2C2D(defbb, pmbb);
              BbResetSq(defbb, goodkingsq);
              repeat
                defsq := BbNextSq(defbb);
                if defsq <> sqnil then
                  begin
                    defman := sqv[defsq];
                    if (defman <> goodpawn) or not checkeropr then
                      GmsPushM2(gms, defsq, checkersq, defman, checkerman)
                    else
                      GmsPushPsCapt(gms, defsq, checkersq, defman, checkerman)
                  end
              until defsq = sqnil
            end;

          { Attempt king capture of a single attacker }

          if singlecheck then
            if BbTestSq(flightbb, checkersq) then
              begin
                GmsPushM2(gms, goodkingsq, checkersq, goodking, checkerman);
                BbResetSq(flightbb, checkersq)
              end;

          { Attempt remaining king moves }

          repeat
            flightsq := BbNextSq(flightbb);
            if flightsq <> sqnil then
              GmsPushM2(gms, goodkingsq, flightsq, goodking, sqv[flightsq])
          until flightsq = sqnil;

          { Attempt interposition against a singleton sweep attacker (all non captures) }

          if singlecheck then
            if BbTestSq(sweep, checkersq) then
              if not BbTestSq(atkfs[goodkingsq], checkersq) then
                begin
                  cvpwbb := pathwaybbvec[goodkingsq, checkersq];

                  { Try non pawn interpositions }

                  pathbb := cvpwbb;
                  repeat
                    pathsq := BbNextSq(pathbb);
                    if pathsq <> sqnil then
                      begin
                        BbAnd2(ipdbb, atkts[pathsq], goodbb);
                        BbAnd2C2D(ipdbb, goodpawnbb);
                        BbAnd2C2D(ipdbb, pmbb);
                        BbResetSq(ipdbb, goodkingsq);
                        repeat
                          ipdsq := BbNextSq(ipdbb);
                          if ipdsq <> sqnil then
                            GmsPushM1(gms, ipdsq, pathsq, sqv[ipdsq])
                        until ipdsq = sqnil
                      end
                  until pathsq = sqnil;

                  { Try pawn interpositions }

                  if not BbIsReset(goodpawnbb) then
                    if not IsSameBfile(goodkingsq, checkersq) then
                      begin

                        { Single square advance pawn interpositions }

                        BbAnd2C2(ipdbb, goodpawnbb, fmbb);
                        repeat
                          ipdsq := BbNextSq(ipdbb);
                          if ipdsq <> sqnil then
                            begin
                              pathsq := advance[ipdsq, advdir];
                              if BbTestSq(cvpwbb, pathsq) then
                                if sqtobrank[pathsq] <> r8brank then
                                  GmsPushM1(gms, ipdsq, pathsq, goodpawn)
                                else
                                  GmsPushPsHold(gms, ipdsq, pathsq, goodpawn)
                            end
                        until ipdsq = sqnil;

                        { Double square advance pawn interpositions }

                        BbAnd2(pathbb, cvpwbb, brankbbvec[r4brank]);
                        if not BbIsReset(pathbb) then
                          begin
                            BbAnd2(ipdbb, goodpawnbb, brankbbvec[r2brank]);
                            BbAnd2C2D(ipdbb, fmbb);
                            repeat
                              ipdsq := BbNextSq(ipdbb);
                              if ipdsq <> sqnil then
                                begin
                                  pathsq := advance[ipdsq, advdir];
                                  if not BbTestSq(merge, pathsq) then
                                    begin
                                      pathsq := advance[pathsq, advdir];
                                      if BbTestSq(pathbb, pathsq) then
                                        GmsPushM1(gms, ipdsq, pathsq, goodpawn)
                                    end
                                end
                            until ipdsq = sqnil
                          end
                      end
                end;

          { Attempt en passant capture }

          if epsq <> sqnil then
            begin
              BbAnd2(defbb, goodpawnbb, pawnatkbbvec[evil, epsq]);
              repeat
                defsq := BbNextSq(defbb);
                if defsq <> sqnil then
                  begin
                    MoveSynthM4(epmove, defsq, epsq, goodpawn, mscepc);
                    if PosIsEnPassantMoveLegal(pos, epmove) then
                      GmsPush(gms, epmove)
                  end
              until defsq = sqnil
            end

        end
    end; { PosGenerateEvasion }

    procedure PosGenerateNoCheck;
      var
        goodkingsq: sqtype;
        goodbb, evilbb, destbb: bbtype;
        frbb, tobb: bbtype;
        frsq, tosq: sqxtype;
        frman: manrtype;
        frbrank: branktype;
        r2brank, r7brank: branktype;
        r2flag, r7flag: Boolean;
        advdir, capdir: dirtype;
        resdir: dirxtype;
        pawnatkbb: bbtype;
        epmove: movetype;
        cast: casttype;
    begin
      with pos, board, bbdb do
        begin

          { Initialize for the good man scan }

          goodkingsq := ksqv[good];
          goodbb := locbc[good];
          evilbb := locbc[evil];
          BbNot1(destbb, goodbb);
          BbAnd2C2(frbb, goodbb, fmbb);
          r2brank := normalbrank[good, brank2];
          r7brank := normalbrank[good, brank7];
          advdir := pawnadvdir[good];

          { Loop once for each possible moving man }

          repeat
            frsq := BbNextSq(frbb);
            if frsq <> sqnil then
              begin

                { Fetch the moving man and process by its piece kind }

                frman := sqv[frsq];
                case mantopiece[frman] of

                  piecep:
                    begin

                      { Set various pre-generation data for this pawn }

                      frbrank := sqtobrank[frsq];
                      r2flag := frbrank = r2brank;
                      r7flag := frbrank = r7brank;
                      if BbTestSq(pmbb, frsq) then
                        resdir := compass[goodkingsq, frsq]
                      else
                        resdir := dirnil;
                      pawnatkbb := pawnatkbbvec[good, frsq];

                      { Pawn noncapture moves (includes noncapture promotions) }

                      if (resdir = dirnil) or IsDirxOrtho(resdir) then
                        begin
                          tosq := advance[frsq, advdir];
                          if not BbTestSq(merge, tosq) then
                            if r7flag then
                              GmsPushPsHold(gms, frsq, tosq, frman)
                            else
                              begin
                                GmsPushM1(gms, frsq, tosq, frman);
                                if r2flag then
                                  begin
                                    tosq := advance[tosq, advdir];
                                    if not BbTestSq(merge, tosq) then
                                      GmsPushM1(gms, frsq, tosq, frman);
                                  end
                              end
                        end;

                      { Pawn capture moves (includes capture promotions; not en passant) }

                      BbAnd2(tobb, pawnatkbb, evilbb);
                      repeat
                        tosq := BbNextSq(tobb);
                        if tosq <> sqnil then
                          begin
                            capdir := compass[frsq, tosq];
                            if (resdir = dirnil) or (resdir = capdir) then
                              if r7flag then
                                GmsPushPsCapt(gms, frsq, tosq, frman, sqv[tosq])
                              else
                                GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                          end
                      until tosq = sqnil;

                      { En passant capture }

                      if epsq <> sqnil then
                        if BbTestSq(pawnatkbb, epsq) then
                          begin
                            MoveSynthM4(epmove, frsq, epsq, frman, mscepc);
                            if PosIsEnPassantMoveLegal(pos, epmove) then
                              GmsPush(gms, epmove)
                          end
                    end;

                  piecen:
                    begin

                      { Regular knight moves }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      repeat
                        tosq := BbNextSq(tobb);
                        if tosq <> sqnil then
                          GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                      until tosq = sqnil
                    end;

                  pieceb, piecer, pieceq:
                    begin

                      { Regular sweeper moves }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      if BbTestSq(pmbb, frsq) then
                        BbAnd2D(tobb, beambbvec[goodkingsq, frsq]);
                      repeat
                        tosq := BbNextSq(tobb);
                        if tosq <> sqnil then
                          GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                      until tosq = sqnil
                    end;

                  piecek:
                    begin

                      { Regular king moves }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      BbAnd2C2D(tobb, atkbc[evil]);
                      repeat
                        tosq := BbNextSq(tobb);
                        if tosq <> sqnil then
                          GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                      until tosq = sqnil;

                      { Castling }

                      if (cavs * colortocavs[good]) <> [] then
                        for cast := colortocastling0[good] to colortocastling1[good] do
                          if PosIsCastlingLegal(pos, cast) then
                            GmsPush(gms, cdrvec[cast].cmov)
                    end

                end { case }
              end
          until frsq = sqnil
        end
    end; { PosGenerateNoCheck }

  begin
    GmsReset(gms);
    if pos.inch then
      PosGenerateEvasion
    else
      PosGenerateNoCheck
  end; { PosGenerate }

  procedure PosGenOnlyGainers(var pos: postype; var gms: gmstype);
    var
      goodkingsq: sqtype;
      goodbb, evilbb: bbtype;
      frbb, tobb: bbtype;
      frsq, tosq: sqxtype;
      frman: manrtype;
      r7brank: branktype;
      r7flag: Boolean;
      advdir, capdir: dirtype;
      resdir: dirxtype;
      pawnatkbb: bbtype;
      epmove: movetype;
  begin
    Assert(not pos.inch, 'PosGenOnlyGainers: good king in check');
    GmsReset(gms);
    with pos, board, bbdb do
      begin

        { Initialize for the good man scan }

        goodkingsq := ksqv[good];
        goodbb := locbc[good];
        evilbb := locbc[evil];
        BbAnd2C2(frbb, goodbb, fmbb);
        r7brank := normalbrank[good, brank7];
        advdir := pawnadvdir[good];

        { Loop once for each possible moving man }

        repeat
          frsq := BbNextSq(frbb);
          if frsq <> sqnil then
            begin

              { Fetch the moving man and process by its piece kind }

              frman := sqv[frsq];
              case mantopiece[frman] of

                piecep:
                  begin

                    { Set various pre-generation data for this pawn }

                    r7flag := sqtobrank[frsq] = r7brank;
                    if BbTestSq(pmbb, frsq) then
                      resdir := compass[goodkingsq, frsq]
                    else
                      resdir := dirnil;
                    pawnatkbb := pawnatkbbvec[good, frsq];

                    { Pawn noncapture promotions }

                    if (resdir = dirnil) or IsDirxOrtho(resdir) then
                      if r7flag then
                        begin
                          tosq := advance[frsq, advdir];
                          if not BbTestSq(merge, tosq) then
                            GmsPushPsHold(gms, frsq, tosq, frman)
                        end;

                    { Pawn capture moves (includes capture promotions; not en passant) }

                    BbAnd2(tobb, pawnatkbb, evilbb);
                    repeat
                      tosq := BbNextSq(tobb);
                      if tosq <> sqnil then
                        begin
                          capdir := compass[frsq, tosq];
                          if (resdir = dirnil) or (resdir = capdir) then
                            if r7flag then
                              GmsPushPsCapt(gms, frsq, tosq, frman, sqv[tosq])
                            else
                              GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                        end
                    until tosq = sqnil;

                    { En passant capture }

                    if epsq <> sqnil then
                      if BbTestSq(pawnatkbb, epsq) then
                        begin
                          MoveSynthM4(epmove, frsq, epsq, frman, mscepc);
                          if PosIsEnPassantMoveLegal(pos, epmove) then
                            GmsPush(gms, epmove)
                        end
                  end;

                piecen:
                  begin

                    { Regular knight capturing moves }

                    BbAnd2(tobb, atkfs[frsq], evilbb);
                    repeat
                      tosq := BbNextSq(tobb);
                      if tosq <> sqnil then
                        GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                    until tosq = sqnil
                  end;

                pieceb, piecer, pieceq:
                  begin

                    { Regular sweeper capturing moves }

                    BbAnd2(tobb, atkfs[frsq], evilbb);
                    if BbTestSq(pmbb, frsq) then
                      BbAnd2D(tobb, beambbvec[goodkingsq, frsq]);
                    repeat
                      tosq := BbNextSq(tobb);
                      if tosq <> sqnil then
                        GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                    until tosq = sqnil
                  end;

                piecek:
                  begin

                    { Regular king capturing moves }

                    BbAnd2(tobb, atkfs[frsq], evilbb);
                    BbAnd2C2D(tobb, atkbc[evil]);
                    repeat
                      tosq := BbNextSq(tobb);
                      if tosq <> sqnil then
                        GmsPushM2(gms, frsq, tosq, frman, sqv[tosq])
                    until tosq = sqnil
                  end

              end { case }
            end
        until frsq = sqnil
      end
  end; { PosGenOnlyGainers }

  procedure PosMarkChecks(var pos: postype; var gms: gmstype); forward;

  procedure PosGenOnlyChecks(var pos: postype; var gms: gmstype);
    var
      altgms: gmstype;
      index: Integer;
  begin
    GmsReset(gms);
    PosGenerate(pos, altgms);
    PosMarkChecks(pos, altgms);
    for index := genmin to altgms.movecount - 1 do
      if MoveFlagTest(altgms.moves[index], mfchck) then
        GmsPush(gms, altgms.moves[index])
  end; { PosGenOnlyChecks }

  function PosCountMoves(var pos: postype): Integer;
    var
      myresult: Integer;

    function PosCountMovesEvasion: Integer;
      var
        myresult: Integer;
        goodkingsq: sqtype;
        goodpawn: manrtype;
        goodbb, goodpawnbb: bbtype;
        r2brank, r4brank, r8brank: branktype;
        advdir: dirtype;
        singlecheck: Boolean;
        checkerbb: bbtype;
        checkersq: sqxtype;
        checkeropr: Boolean;
        flightbb: bbtype;
        atkbb: bbtype;
        atksq: sqxtype;
        defbb: bbtype;
        defsq: sqxtype;
        shadowsq: sqxtype;
        cvpwbb: bbtype;
        pathbb: bbtype;
        pathsq: sqxtype;
        ipdbb: bbtype;
        ipdsq: sqxtype;
        epmove: movetype;
    begin
      with pos, board, bbdb do
        begin
          myresult := 0;

          { Set various local constant values }

          goodkingsq := ksqv[good];
          goodpawn := synthpawn[good];
          goodbb := locbc[good];
          goodpawnbb := locbm[goodpawn];
          r2brank := normalbrank[good, brank2];
          r4brank := normalbrank[good, brank4];
          r8brank := normalbrank[good, brank8];
          advdir := pawnadvdir[good];
          singlecheck := not dbch;
          BbAnd2(checkerbb, locbc[evil], atkts[goodkingsq]);

          { Set various checker data local constant values according to double check status }

          if singlecheck then
            begin
              checkersq := BbFirstSq(checkerbb);
              checkeropr := sqtobrank[checkersq] = r8brank
            end
          else
            begin
              checkersq := sqnil;
              checkeropr := False
            end;

          { Initialize the king flight squares bitboard }

          flightbb := kingatkbbvec[goodkingsq];
          BbAnd2C2D(flightbb, goodbb);
          BbAnd2C2D(flightbb, atkbc[evil]);

          { Remove any shadow squares from the flight bitboard }

          atkbb := checkerbb;
          repeat
            atksq := BbNextSq(atkbb);
            if atksq <> sqnil then
              if BbTestSq(sweep, atksq) then
                begin
                  shadowsq := shadows[atksq, goodkingsq];
                  if shadowsq <> sqnil then
                    BbResetSq(flightbb, shadowsq)
                end
          until atksq = sqnil;

          { Attempt capture of a singleton attacker (no king moves, no en passant) }

          if singlecheck then
            begin
              BbAnd2(defbb, atkts[checkersq], goodbb);
              BbAnd2C2D(defbb, pmbb);
              BbResetSq(defbb, goodkingsq);
              repeat
                defsq := BbNextSq(defbb);
                if defsq <> sqnil then
                  if (sqv[defsq] <> goodpawn) or not checkeropr then
                    Inc(myresult)
                  else
                    Inc(myresult, 4)
              until defsq = sqnil
            end;

          { Attempt king capture of a single attacker }

          if singlecheck then
            if BbTestSq(flightbb, checkersq) then
              begin
                Inc(myresult);
                BbResetSq(flightbb, checkersq)
              end;

          { Attempt remaining king moves }

          Inc(myresult, BbCount(flightbb));

          { Attempt interposition against a singleton sweep attacker (all non captures) }

          if singlecheck then
            if BbTestSq(sweep, checkersq) then
              if not BbTestSq(atkfs[goodkingsq], checkersq) then
                begin
                  cvpwbb := pathwaybbvec[goodkingsq, checkersq];

                  { Try non pawn interpositions }

                  pathbb := cvpwbb;
                  repeat
                    pathsq := BbNextSq(pathbb);
                    if pathsq <> sqnil then
                      begin
                        BbAnd2(ipdbb, atkts[pathsq], goodbb);
                        BbAnd2C2D(ipdbb, goodpawnbb);
                        BbAnd2C2D(ipdbb, pmbb);
                        BbResetSq(ipdbb, goodkingsq);
                        Inc(myresult, BbCount(ipdbb))
                      end
                  until pathsq = sqnil;

                  { Try pawn interpositions }

                  if not BbIsReset(goodpawnbb) then
                    if not IsSameBfile(goodkingsq, checkersq) then
                      begin

                        { Single square advance pawn interpositions }

                        BbAnd2C2(ipdbb, goodpawnbb, fmbb);
                        repeat
                          ipdsq := BbNextSq(ipdbb);
                          if ipdsq <> sqnil then
                            begin
                              pathsq := advance[ipdsq, advdir];
                              if BbTestSq(cvpwbb, pathsq) then
                                if sqtobrank[pathsq] <> r8brank then
                                  Inc(myresult)
                                else
                                  Inc(myresult, 4)
                            end
                        until ipdsq = sqnil;

                        { Double square advance pawn interpositions }

                        BbAnd2(pathbb, cvpwbb, brankbbvec[r4brank]);
                        if not BbIsReset(pathbb) then
                          begin
                            BbAnd2(ipdbb, goodpawnbb, brankbbvec[r2brank]);
                            BbAnd2C2D(ipdbb, fmbb);
                            repeat
                              ipdsq := BbNextSq(ipdbb);
                              if ipdsq <> sqnil then
                                begin
                                  pathsq := advance[ipdsq, advdir];
                                  if not BbTestSq(merge, pathsq) then
                                    begin
                                      pathsq := advance[pathsq, advdir];
                                      if BbTestSq(pathbb, pathsq) then
                                        Inc(myresult)
                                    end
                                end
                            until ipdsq = sqnil
                          end
                      end
                end;

          { Attempt en passant capture }

          if epsq <> sqnil then
            begin
              BbAnd2(defbb, goodpawnbb, pawnatkbbvec[evil, epsq]);
              repeat
                defsq := BbNextSq(defbb);
                if defsq <> sqnil then
                  begin
                    MoveSynthM4(epmove, defsq, epsq, goodpawn, mscepc);
                    if PosIsEnPassantMoveLegal(pos, epmove) then
                      Inc(myresult)
                  end
              until defsq = sqnil
            end

        end;
      PosCountMovesEvasion := myresult
    end; { PosCountMovesEvasion }

    function PosCountMovesNoCheck: Integer;
      var
        myresult: Integer;
        goodkingsq: sqtype;
        goodbb, evilbb, destbb: bbtype;
        frbb, tobb: bbtype;
        frsq, tosq: sqxtype;
        frman: manrtype;
        frbrank: branktype;
        r2brank, r7brank: branktype;
        r2flag, r7flag: Boolean;
        advdir, capdir: dirtype;
        resdir: dirxtype;
        pawnatkbb: bbtype;
        epmove: movetype;
        cast: casttype;
    begin
      with pos, board, bbdb do
        begin
          myresult := 0;

          { Initialize for the good man scan }

          goodkingsq := ksqv[good];
          goodbb := locbc[good];
          evilbb := locbc[evil];
          BbNot1(destbb, goodbb);
          BbAnd2C2(frbb, goodbb, fmbb);
          r2brank := normalbrank[good, brank2];
          r7brank := normalbrank[good, brank7];
          advdir := pawnadvdir[good];

          { Loop once for each possible moving man }

          repeat
            frsq := BbNextSq(frbb);
            if frsq <> sqnil then
              begin

                { Fetch the moving man and process by its piece kind }

                frman := sqv[frsq];
                case mantopiece[frman] of

                  piecep:
                    begin

                      { Set various pre-generation data for this pawn }

                      frbrank := sqtobrank[frsq];
                      r2flag := frbrank = r2brank;
                      r7flag := frbrank = r7brank;
                      if BbTestSq(pmbb, frsq) then
                        resdir := compass[goodkingsq, frsq]
                      else
                        resdir := dirnil;
                      pawnatkbb := pawnatkbbvec[good, frsq];

                      { Pawn noncapture moves (includes noncapture promotions) }

                      if (resdir = dirnil) or IsDirxOrtho(resdir) then
                        begin
                          tosq := advance[frsq, advdir];
                          if not BbTestSq(merge, tosq) then
                            if r7flag then Inc(myresult, 4)
                            else
                              begin
                                Inc(myresult);
                                if r2flag then
                                  begin
                                    tosq := advance[tosq, advdir];
                                    if not BbTestSq(merge, tosq) then
                                      Inc(myresult);
                                  end
                              end
                        end;

                      { Pawn capture moves (includes capture promotions; not en passant) }

                      BbAnd2(tobb, pawnatkbb, evilbb);
                      repeat
                        tosq := BbNextSq(tobb);
                        if tosq <> sqnil then
                          begin
                            capdir := compass[frsq, tosq];
                            if (resdir = dirnil) or (resdir = capdir) then
                              if r7flag then
                                Inc(myresult, 4)
                              else
                                Inc(myresult)
                          end
                      until tosq = sqnil;

                      { En passant capture }

                      if epsq <> sqnil then
                        if BbTestSq(pawnatkbb, epsq) then
                          begin
                            MoveSynthM4(epmove, frsq, epsq, frman, mscepc);
                            if PosIsEnPassantMoveLegal(pos, epmove) then
                              Inc(myresult)
                          end
                    end;

                  piecen:
                    begin

                      { Regular knight moves }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      Inc(myresult, BbCount(tobb))
                    end;

                  pieceb, piecer, pieceq:
                    begin

                      { Regular sweeper moves }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      if BbTestSq(pmbb, frsq) then
                        BbAnd2D(tobb, beambbvec[goodkingsq, frsq]);
                      Inc(myresult, BbCount(tobb))
                    end;

                  piecek:
                    begin

                      { Regular king moves }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      BbAnd2C2D(tobb, atkbc[evil]);
                      Inc(myresult, BbCount(tobb));

                      { Castling }

                      if (cavs * colortocavs[good]) <> [] then
                        for cast := colortocastling0[good] to colortocastling1[good] do
                          if PosIsCastlingLegal(pos, cast) then
                            Inc(myresult)
                    end

                end { case }
              end
          until frsq = sqnil
        end;
      PosCountMovesNoCheck := myresult
    end; { PosCountMovesNoCheck }

  begin
    if pos.inch then
      myresult := PosCountMovesEvasion
    else
      myresult := PosCountMovesNoCheck;
    PosCountMoves := myresult
  end; { PosCountMoves }

  function PosHasNoMoves(var pos: postype): Boolean;
    var
      myresult: Boolean;

    function PosHasNoMovesEvasion: Boolean;
      var
        myresult: Boolean;
        goodkingsq: sqtype;
        goodpawn: manrtype;
        goodbb, goodpawnbb: bbtype;
        r2brank, r4brank: branktype;
        advdir: dirtype;
        singlecheck: Boolean;
        checkerbb: bbtype;
        checkersq: sqxtype;
        flightbb: bbtype;
        atkbb: bbtype;
        atksq: sqxtype;
        defbb: bbtype;
        defsq: sqxtype;
        shadowsq: sqxtype;
        cvpwbb: bbtype;
        pathbb: bbtype;
        pathsq: sqxtype;
        ipdbb: bbtype;
        ipdsq: sqxtype;
        epmove: movetype;
    begin

      { The king is in check; this routine acts as a checkmate detector }

      with pos, board, bbdb do
        begin
          myresult := True;

          { Set various local constant values }

          goodkingsq := ksqv[good];
          goodpawn := synthpawn[good];
          goodbb := locbc[good];
          goodpawnbb := locbm[goodpawn];
          r2brank := normalbrank[good, brank2];
          r4brank := normalbrank[good, brank4];
          advdir := pawnadvdir[good];
          singlecheck := not dbch;
          BbAnd2(checkerbb, locbc[evil], atkts[goodkingsq]);

          { Set various checker data local constant values according to double check status }

          if singlecheck then
            checkersq := BbFirstSq(checkerbb)
          else
            checkersq := sqnil;

          { Initialize the king flight squares bitboard }

          flightbb := kingatkbbvec[goodkingsq];
          BbAnd2C2D(flightbb, goodbb);
          BbAnd2C2D(flightbb, atkbc[evil]);

          { Remove any shadow squares from the flight bitboard }

          atkbb := checkerbb;
          repeat
            atksq := BbNextSq(atkbb);
            if atksq <> sqnil then
              if BbTestSq(sweep, atksq) then
                begin
                  shadowsq := shadows[atksq, goodkingsq];
                  if shadowsq <> sqnil then
                    BbResetSq(flightbb, shadowsq)
                end
          until atksq = sqnil;

          { Attempt capture of a singleton attacker (no king moves, no en passant) }

          if singlecheck then
            begin
              BbAnd2(defbb, atkts[checkersq], goodbb);
              BbAnd2C2D(defbb, pmbb);
              BbResetSq(defbb, goodkingsq);
              if not BbIsReset(defbb) then
                myresult := False
            end;

          { Attempt king capture of a single attacker }

          if myresult and singlecheck then
            if BbTestSq(flightbb, checkersq) then
              begin
                myresult := False;
                BbResetSq(flightbb, checkersq)
              end;

          { Attempt remaining king moves }

          if myresult and not BbIsReset(flightbb) then
            myresult := False;

          { Attempt interposition against a singleton sweep attacker (all non captures) }

          if myresult and singlecheck then
            if BbTestSq(sweep, checkersq) then
              if not BbTestSq(atkfs[goodkingsq], checkersq) then
                begin
                  cvpwbb := pathwaybbvec[goodkingsq, checkersq];

                  { Try non pawn interpositions }

                  pathbb := cvpwbb;
                  repeat
                    pathsq := BbNextSq(pathbb);
                    if pathsq <> sqnil then
                      begin
                        BbAnd2(ipdbb, atkts[pathsq], goodbb);
                        BbAnd2C2D(ipdbb, goodpawnbb);
                        BbAnd2C2D(ipdbb, pmbb);
                        BbResetSq(ipdbb, goodkingsq);
                        if not BbIsReset(ipdbb) then
                          myresult := False
                      end
                  until (pathsq = sqnil) or not myresult;

                  { Try pawn interpositions }

                  if myresult and not BbIsReset(goodpawnbb) then
                    if not IsSameBfile(goodkingsq, checkersq) then
                      begin

                        { Single square advance pawn interpositions }

                        BbAnd2C2(ipdbb, goodpawnbb, fmbb);
                        repeat
                          ipdsq := BbNextSq(ipdbb);
                          if ipdsq <> sqnil then
                            begin
                              pathsq := advance[ipdsq, advdir];
                              if BbTestSq(cvpwbb, pathsq) then
                                myresult := False
                            end
                        until (ipdsq = sqnil) or not myresult;

                        { Double square advance pawn interpositions }

                        if myresult then
                          begin
                            BbAnd2(pathbb, cvpwbb, brankbbvec[r4brank]);
                            if not BbIsReset(pathbb) then
                              begin
                                BbAnd2(ipdbb, goodpawnbb, brankbbvec[r2brank]);
                                BbAnd2C2D(ipdbb, fmbb);
                                repeat
                                  ipdsq := BbNextSq(ipdbb);
                                  if ipdsq <> sqnil then
                                    begin
                                      pathsq := advance[ipdsq, advdir];
                                      if not BbTestSq(merge, pathsq) then
                                        begin
                                          pathsq := advance[pathsq, advdir];
                                          if BbTestSq(pathbb, pathsq) then
                                            myresult := False
                                        end
                                    end
                                until (ipdsq = sqnil) or not myresult
                              end
                          end
                      end
                end;

          { Attempt en passant capture }

          if myresult and (epsq <> sqnil) then
            begin
              BbAnd2(defbb, goodpawnbb, pawnatkbbvec[evil, epsq]);
              repeat
                defsq := BbNextSq(defbb);
                if defsq <> sqnil then
                  begin
                    MoveSynthM4(epmove, defsq, epsq, goodpawn, mscepc);
                    if PosIsEnPassantMoveLegal(pos, epmove) then
                      myresult := False
                  end
              until (defsq = sqnil) or not myresult
            end

        end;
      PosHasNoMovesEvasion := myresult
    end; { PosHasNoMovesEvasion }

    function PosHasNoMovesNoCheck: Boolean;
      var
        myresult: Boolean;
        goodkingsq: sqtype;
        goodbb, evilbb, destbb: bbtype;
        frbb, tobb: bbtype;
        frsq, tosq: sqxtype;
        frman: manrtype;
        advdir, capdir: dirtype;
        resdir: dirxtype;
        pawnatkbb: bbtype;
        epmove: movetype;
    begin

      { The king is not in check; this routine acts as a stalemate detector }

      with pos, board, bbdb do
        begin
          myresult := True;

          { Initialize for the good man scan }

          goodkingsq := ksqv[good];
          goodbb := locbc[good];
          evilbb := locbc[evil];
          BbNot1(destbb, goodbb);
          BbAnd2C2(frbb, goodbb, fmbb);
          advdir := pawnadvdir[good];

          { Loop once for each possible moving man; stop early if at least one move possible }

          repeat
            frsq := BbNextSq(frbb);
            if frsq <> sqnil then
              begin

                { Fetch the moving man and process by its piece kind }

                frman := sqv[frsq];
                case mantopiece[frman] of

                  piecep:
                    begin

                      { Set various pre-generation data for this pawn }

                      if BbTestSq(pmbb, frsq) then
                        resdir := compass[goodkingsq, frsq]
                      else
                        resdir := dirnil;
                      pawnatkbb := pawnatkbbvec[good, frsq];

                      { Pawn noncapture moves (includes noncapture promotions) }

                      if (resdir = dirnil) or IsDirxOrtho(resdir) then
                        begin
                          tosq := advance[frsq, advdir];
                          if not BbTestSq(merge, tosq) then
                            myresult := False
                        end;

                      { Pawn capture moves (includes capture promotions; not en passant) }

                      if myresult then
                        begin
                          BbAnd2(tobb, pawnatkbb, evilbb);
                          repeat
                            tosq := BbNextSq(tobb);
                            if tosq <> sqnil then
                              begin
                                capdir := compass[frsq, tosq];
                                if (resdir = dirnil) or (resdir = capdir) then
                                  myresult := False
                              end
                          until (tosq = sqnil) or not myresult
                        end;

                      { En passant capture }

                      if myresult and (epsq <> sqnil) then
                        if BbTestSq(pawnatkbb, epsq) then
                          begin
                            MoveSynthM4(epmove, frsq, epsq, frman, mscepc);
                            if PosIsEnPassantMoveLegal(pos, epmove) then
                              myresult := False
                          end
                    end;

                  piecen:
                    begin

                      { Regular knight moves }

                      if not BbNI2(atkfs[frsq], destbb) then
                        myresult := False
                    end;

                  pieceb, piecer, pieceq:
                    begin

                      { Regular sweeper moves }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      if BbTestSq(pmbb, frsq) then
                        BbAnd2D(tobb, beambbvec[goodkingsq, frsq]);
                      if not BbIsReset(tobb) then
                        myresult := False
                    end;

                  piecek:
                    begin

                      { Regular king moves; castling is safely skipped }

                      BbAnd2(tobb, atkfs[frsq], destbb);
                      BbAnd2C2D(tobb, atkbc[evil]);
                      if not BbIsReset(tobb) then
                        myresult := False;
                    end

                end { case }
              end
          until (frsq = sqnil) or not myresult
        end;
      PosHasNoMovesNoCheck := myresult
    end; { PosHasNoMovesNoCheck }

  begin

    { Depending on check status, this routine detects either checkmate or stalemate }

    if pos.inch then
      myresult := PosHasNoMovesEvasion
    else
      myresult := PosHasNoMovesNoCheck;
    PosHasNoMoves := myresult
  end; { PosHasNoMoves }

  function PosCanCancelEpSq(var pos: postype): Boolean;
    var
      myresult: Boolean;
      goodpawn: manrtype;
      defbb: bbtype;
      defsq: sqxtype;
      epmove: movetype;
  begin
    with pos, bbdb do
      begin
        myresult := True;
        goodpawn := synthpawn[good];
        BbAnd2(defbb, locbm[goodpawn], pawnatkbbvec[evil, epsq]);
        repeat
          defsq := BbNextSq(defbb);
          if defsq <> sqnil then
            begin
              MoveSynthM4(epmove, defsq, epsq, goodpawn, mscepc);
              if PosIsEnPassantMoveLegal(pos, epmove) then
                myresult := False
            end
        until (defsq = sqnil) or not myresult
      end;
    PosCanCancelEpSq := myresult
  end; { PosCanCancelEpSq }

  procedure PosExecute(var pos: postype; var move: movetype);
    var
      spevptr: spevptrtype;
      cast: casttype;
      isnotnull: Boolean;
  begin
    with pos do
      begin

        { Ensure at least one spev record on the free spev list }

        if freespevlist.tail = nil then
          begin
            New(spevptr);
            SpevListAppendTail(freespevlist, spevptr)
          end;

        { Detach a spev record from the tail of the free spev list }

        spevptr := SpevListDetachTail(freespevlist);

        { Load into the saved position environment values node }

        with spevptr^ do
          begin
            spevmove := move;
            spevgood := good;
            spevevil := evil;
            spevcavs := cavs;
            spevepsq := epsq;
            spevhmvc := hmvc;
            spevfmvn := fmvn;
            spevinch := inch;
            spevdbch := dbch;
            spevpmbb := pmbb;
            spevfmbb := fmbb;
            spevmphc := mphc
          end;

        { Append the saved position environment values node to the used spev list }

        SpevListAppendTail(usedspevlist, spevptr);

        { Make the move }

        with move do
          begin

            { Perform forward motion only for a non-null move }

            isnotnull := not MoveFlagTest(move, mfnull);
            if isnotnull then
              begin
                case msc of
                  mscreg:
                    if toman <> manvv then
                      PosCaptureMan(pos, frsq, tosq)
                    else
                      PosMovMan(pos, frsq, tosq);
                  mscepc:
                    begin
                      PosDelMan(pos, advance[tosq, pawnadvdir[evil]]);
                      PosMovMan(pos, frsq, tosq)
                    end;
                  msccqs, msccks:
                    begin
                      PosMovMan(pos, frsq, tosq);
                      with cdrvec[MapColorMscToCast(good, msc)] do
                        PosMovMan(pos, r0sq, r1sq)
                    end;
                  mscppn, mscppb, mscppr, mscppq:
                    begin
                      if toman <> manvv then
                        PosDelMan(pos, tosq);
                      PosDelMan(pos, frsq);
                      PosAddMan(pos, colorpiecetoman[good, msctopiece[msc]], tosq)
                    end
                end { case }
              end;

            { Update: colors }

            good := othercolor[good];
            evil := othercolor[evil];

            { Update: castling availability values set }

            if isnotnull then
              if cavs <> [] then
                for cast := castmin to castmax do
                  with cdrvec[cast] do
                    if cast in cavs then
                      if (frsq = k0sq) or (frsq = r0sq) or (tosq = r0sq) then
                        begin
                          cavs := cavs - [cast];
                          HashXor2D(mphc, hashcastlingvec[cast])
                        end;

            { Update: en passant target square }

            if epsq <> sqnil then
              begin
                HashXor2D(mphc, hashepfilevec[sqtobfile[epsq]]);
                epsq := sqnil
              end;
            if isnotnull then
              if (frman in pawnmanset) and ((frsq xor tosq) = (bfilelen * 2)) then
                if not BbNI2(bbdb.locbm[synthpawn[good]], lateralbbvec[tosq]) then
                  begin
                    epsq := advance[frsq, pawnadvdir[evil]];
                    if PosCanCancelEpSq(pos) then
                      epsq := sqnil
                    else
                      HashXor2D(mphc, hashepfilevec[sqtobfile[epsq]])
                  end;

            { Update: half move counter and full move number }

            if isnotnull then
              if MoveIsHmvcReset(move) then
                hmvc := 0
              else
                Inc(hmvc);
            if good = colorw then
              Inc(fmvn);

            { Update: checking statuses and pin data bitboards }

            PosRebuild(pos)
          end;

        { Sanity test: evil king not in check }

        Assert(not BbTestSq(bbdb.atkbc[good], ksqv[evil]), 'PosExecute: evil king in check')
      end
  end; { PosExecute }

  procedure PosRetract(var pos: postype);
    var
      move: movetype;
      savecavs: castsettype;
      saveepsq: sqxtype;
      priormphc: hashtype;
      spevptr: spevptrtype;
      cast: casttype;
  begin
    with pos do
      begin

        { Preserve the pre-retraction castling availability set and en passant target square }

        savecavs := cavs;
        saveepsq := epsq;

        { Detach the saved position environment values node from the used spev list }

        spevptr := SpevListDetachTail(usedspevlist);

        { Unload from the saved position environment values node }

        with spevptr^ do
          begin
            move := spevmove;
            good := spevgood;
            evil := spevevil;
            cavs := spevcavs;
            epsq := spevepsq;
            hmvc := spevhmvc;
            fmvn := spevfmvn;
            inch := spevinch;
            dbch := spevdbch;
            pmbb := spevpmbb;
            fmbb := spevfmbb;
            priormphc := spevmphc
          end;

        { Append the saved position environment values node to the free spev list }

        SpevListAppendTail(freespevlist, spevptr);

        { Apply any needed correction to the castling component of the main position hash }

        if savecavs <> cavs then
          for cast := castmin to castmax do
            if (cast in cavs) <> (cast in savecavs) then
              HashXor2D(mphc, hashcastlingvec[cast]);

        { Apply any needed correction to the en passant component of the main position hash }

        if saveepsq <> epsq then
          begin
            if saveepsq <> sqnil then
              HashXor2D(mphc, hashepfilevec[sqtobfile[saveepsq]]);
            if epsq <> sqnil then
              HashXor2D(mphc, hashepfilevec[sqtobfile[epsq]])
          end;

        { Unmake the move }

        with move do
          begin

            { Perform backward motion only for a non-null move }

            if not MoveFlagTest(move, mfnull) then
              begin
                case msc of
                  mscreg:
                    if toman <> manvv then
                      PosRevCaptMan(pos, toman, frsq, tosq)
                    else
                      PosMovMan(pos, tosq, frsq);
                  mscepc:
                    begin
                      PosMovMan(pos, tosq, frsq);
                      PosAddMan(pos, synthpawn[evil], advance[tosq, pawnadvdir[evil]])
                    end;
                  msccqs, msccks:
                    begin
                      with cdrvec[MapColorMscToCast(good, msc)] do
                        PosMovMan(pos, r1sq, r0sq);
                      PosMovMan(pos, tosq, frsq)
                    end;
                  mscppn, mscppb, mscppr, mscppq:
                    begin
                      PosDelMan(pos, tosq);
                      PosAddMan(pos, frman, frsq);
                      if toman <> manvv then
                        PosAddMan(pos, toman, tosq)
                    end
                end { case }
              end
          end;

          { Sanity test: main position hash code restoration }

          Assert(HashEq(priormphc, mphc), 'PosRetract: mphc fault')
      end
  end; { PosRetract }

  procedure PosRetractAll(var pos: postype);
  begin
    with pos do
      while usedspevlist.head <> nil do
        PosRetract(pos)
  end; { PosRetractAll }

  procedure PosReset(var pos: postype);
  begin
    PosRetractAll(pos);
    PosClear(pos)
  end; { PosReset }

  procedure PosApplyCavsHashes(var pos: postype);
    var
      cast: casttype;
  begin
    with pos do
      for cast := castmin to castmax do
        if cast in cavs then
          HashXor2D(mphc, hashcastlingvec[cast])
  end; { PosApplyCavsHashes }

  procedure PosLoadFromComponents(
      var pos: postype; var myboard: boardtype;
      mygood: colorrtype; mycavs: castsettype; myepsq: sqxtype; myhmvc: hmvctype; myfmvn: fmvntype);
    var
      sq: sqtype;
      man: mantype;
  begin
    with pos do
      begin
        PosReset(pos);
        good := mygood;
        evil := othercolor[mygood];
        cavs := mycavs;
        epsq := myepsq;
        hmvc := myhmvc;
        fmvn := myfmvn;
        for sq := sqmin to sqmax do
          begin
            man := myboard.sqv[sq];
            if man <> manvv then
              PosAddMan(pos, man, sq)
          end;
        PosApplyCavsHashes(pos);
        if epsq <> sqnil then
          if PosCanCancelEpSq(pos) then
            epsq := sqnil
          else
            HashXor2D(mphc, hashepfilevec[sqtobfile[epsq]]);
        ifen := PosEncode(pos);
        PosRebuild(pos)
      end
  end; { PosLoadFromComponents }

  procedure PosLoadInitialArray(var pos: postype);
  begin
    PosLoadFromComponents(pos, startboard, startgood, startcavs, startepsq, starthmvc, startfmvn)
  end; { PosLoadInitialArray }

  function PosProbeTablebaseSignatureVector(var pos: postype): tbcmsxtype;
    var
      myresult: tbcmsxtype;
      b0, b1, probe: si32type;
  begin
    myresult := tbcmsnil;
    b0 := tbcmsmin;
    b1 := tbcmsmax;
    repeat
      probe := (b0 + b1) div 2;
      if pos.msig = tbmsmvec[probe].msig then
        myresult := tbcmstype(probe)
      else
        if pos.msig < tbmsmvec[probe].msig then
          b1 := probe - 1
        else
          b0 := probe + 1
    until (myresult <> tbcmsnil) or (b0 > b1);
    PosProbeTablebaseSignatureVector := myresult
  end; { PosProbeTablebaseSignatureVector }

  function PosIsCheckmate(var pos: postype): Boolean; inline;
    var
      myresult: Boolean;
  begin
    if not pos.inch then
      myresult := False
    else
      myresult := PosHasNoMoves(pos);
    PosIsCheckmate := myresult
  end; { PosIsCheckmate }

  function PosIsStalemate(var pos: postype): Boolean; inline;
    var
      myresult: Boolean;
  begin
    if pos.inch then
      myresult := False
    else
      myresult := PosHasNoMoves(pos);
    PosIsStalemate := myresult
  end; { PosIsStalemate }

  function PosIsDrawByFiftyMoves(var pos: postype): Boolean; inline;
  begin
    PosIsDrawByFiftyMoves := pos.hmvc >= 100
  end; { PosIsDrawByFiftyMoves }

  function PosIsDrawByInsufficient(var pos: postype): Boolean;
  begin
    PosIsDrawByInsufficient := not CensusForce(pos.census)
  end; { PosIsDrawByInsufficient }

  function PosCalcRepCount(var pos: postype; limit: Integer): Integer;
    var
      myresult: Integer;
      count: hmvctype;
      spevptr: spevptrtype;
  begin
    with pos do
      begin
        myresult := 0;
        count := 0;
        spevptr := usedspevlist.tail;
        while (myresult < limit) and (count < hmvc) and (spevptr <> nil) do
          begin
            if Odd(count) then
              if HashEq(spevptr^.spevmphc, mphc) then
                Inc(myresult);
            Inc(count);
            spevptr := spevptr^.prev
          end
      end;
    PosCalcRepCount := myresult
  end; { PosCalcRepCount }

  function PosIsRepeated(var pos: postype): Boolean; inline;
    var
      myresult: Boolean;
  begin
    if pos.hmvc < 4 then
      myresult := False
    else
      myresult := PosCalcRepCount(pos, 1) = 1;
    PosIsRepeated := myresult
  end; { PosIsRepeated }

  function PosIsDrawByRepetition(var pos: postype): Boolean; inline;
    var
      myresult: Boolean;
  begin
    if pos.hmvc < 8 then
      myresult := False
    else
      myresult := PosCalcRepCount(pos, 2) = 2;
    PosIsDrawByRepetition := myresult
  end; { PosIsDrawByRepetition }

  function PosIsDrawFIR(var pos: postype): Boolean;
  begin
    PosIsDrawFIR :=
        PosIsDrawByFiftyMoves(pos) or PosIsDrawByInsufficient(pos) or PosIsDrawByRepetition(pos)
  end; { PosIsDrawFIR }

  function PosIsDraw(var pos: postype): Boolean;
  begin
    PosIsDraw := PosIsDrawFIR(pos) or PosIsStalemate(pos)
  end; { PosIsDraw }

  function PosCalcGt(var pos: postype): gttype;
    var
      myresult: gttype;
  begin
    if PosHasNoMoves(pos) then
      if pos.inch then
        myresult := gtcheckmate
      else
        myresult := gtstalemate
    else
      if PosIsDrawByFiftyMoves(pos) then
        myresult := gtfiftymoves
      else
        if PosIsDrawByInsufficient(pos) then
          myresult := gtinsufficient
        else
          if PosIsDrawByRepetition(pos) then
            myresult := gtrepetition
          else
            myresult := gtunterminated;
    PosCalcGt := myresult
  end; { PosCalcGt }

  function PosCalcGr(var pos: postype): grtype;
  begin
    PosCalcGr := colorgttogr[pos.good, PosCalcGt(pos)]
  end; { PosCalcGr }

  function PosIsGameOver(var pos: postype): Boolean;
  begin
    PosIsGameOver := PosCalcGt(pos) <> gtunterminated
  end; { PosIsGameOver }

  procedure PosMarkChecks(var pos: postype; var gms: gmstype);
    var
      evilkingsq: sqtype;
      index: Integer;
      runway: runwaytype;
      check: Boolean;
      hfrsq: sqxtype;
      frpiece: piecetype;
      disco: Boolean;
      beambb: bbtype;
  begin
    with pos, bbdb, gms, runway do
      begin
        PosBuildRunway(pos, runway);
        evilkingsq := ksqv[evil];
        hfrsq := sqnil;
        frpiece := piecev;
        disco := False;
        BbReset(beambb);
        for index := 0 to movecount - 1 do
          with moves[index] do
            begin

              { Set up for a new move }

              check := False;
              if hfrsq <> frsq then
                begin
                  hfrsq := frsq;
                  frpiece := mantopiece[frman];
                  disco := BbTestSq(disbb, frsq);
                  beambb := beambbvec[evilkingsq, frsq]
                end;

              { Process by moving piece kind }

              case frpiece of
                piecep:
                  case msc of
                    mscreg:
                      if BbTestSq(prwbb, tosq) then
                        check := True
                      else
                        if disco and not BbTestSq(beambb, tosq) then
                          check := True;
                    mscepc:
                      if PosIsEnPassantMoveChecking(pos, moves[index]) then
                        check := True;
                    mscppn:
                      if disco or BbTestSq(nrwbb, tosq) then
                        check := True;
                    mscppb:
                      if disco or BbTestSq(brwbb, tosq) then
                        check := True
                      else
                        if toman <> manvv then
                          if compass[frsq, tosq] = compass[evilkingsq, frsq] then
                            if BbNI2(merge, pathwaybbvec[evilkingsq, frsq]) then
                              check := True;
                    mscppr:
                      if disco or BbTestSq(rrwbb, tosq) then
                        check := True
                      else
                        if toman = manvv then
                          if compass[frsq, tosq] = compass[evilkingsq, frsq] then
                            if BbNI2(merge, pathwaybbvec[evilkingsq, frsq]) then
                              check := True;
                    mscppq:
                      if disco or BbTestSq(qrwbb, tosq) then
                        check := True
                      else
                        if compass[frsq, tosq] = compass[evilkingsq, frsq] then
                          if BbNI2(merge, pathwaybbvec[evilkingsq, frsq]) then
                            check := True
                  end; { case }
                piecen:
                  if disco or BbTestSq(nrwbb, tosq) then
                    check := True;
                pieceb:
                  if disco or BbTestSq(brwbb, tosq) then
                    check := True;
                piecer:
                  if disco or BbTestSq(rrwbb, tosq) then
                    check := True;
                pieceq:
                  if BbTestSq(qrwbb, tosq) then
                    check := True;
                piecek:
                  case msc of
                    mscreg:
                      if disco and not BbTestSq(beambb, tosq) then
                        check := True;
                    msccqs, msccks:
                      if PosIsCastlingChecking(pos, MapColorMscToCast(good, msc)) then
                        check := True
                  end { case }
              end; { case }
              if check then
                MoveFlagSet(moves[index], mfchck)
            end
      end
  end; { PosMarkChecks }

  procedure PosMarkCheckmates(var pos: postype; var gms: gmstype);
    var
      index: Integer;
  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        if MoveFlagTest(moves[index], mfchck) then
          begin
            PosExecute(pos, moves[index]);
            if PosHasNoMoves(pos) then
              begin
                MoveFlagSet(moves[index], mfchmt);
                MoveSetCertain(moves[index], svmatein1)
              end;
            PosRetract(pos)
          end
  end; { PosMarkCheckmates }

  procedure PosMarkDisambiguation(var pos: postype; var gms: gmstype);
    var
      i0, i1: Integer;
      frman: manrtype;
      frbfile: bfiletype;
      frbrank: branktype;
      toc: array [sqtype] of Integer;
      frsq, tosq, altfrsq: sqtype;
      skipmanset: mansettype;
      mbfc, mbrc, msqc: Integer;
  begin
    with pos, gms do
      begin
        skipmanset := [synthpawn[good], synthking[good]];
        for frman := synthknight[good] to synthqueen[good] do
          if census.mic[frman] < 2 then
            skipmanset := skipmanset + [frman];
        for tosq := sqmin to sqmax do
          toc[tosq] := 0;
        for i0 := 0 to movecount - 1 do
          Inc(toc[moves[i0].tosq]);

        { Outer loop }

        for i0 := 0 to movecount - 1 do
          begin
            frman := moves[i0].frman;
            if not (frman in skipmanset) then
              begin
                tosq := moves[i0].tosq;
                if toc[tosq] > 1 then
                  begin
                    mbfc := 0;
                    mbrc := 0;
                    msqc := 0;
                    frsq := moves[i0].frsq;
                    frbfile := sqtobfile[frsq];
                    frbrank := sqtobrank[frsq];

                    { Inner loop }

                    for i1 := 0 to movecount - 1 do
                      if moves[i1].frsq <> frsq then
                        if moves[i1].tosq = tosq then
                          if moves[i1].frman = frman then
                            begin
                              Inc(msqc);
                              altfrsq := moves[i1].frsq;
                              if frbfile = sqtobfile[altfrsq] then
                                Inc(mbfc);
                              if frbrank = sqtobrank[altfrsq] then
                                Inc(mbrc)
                            end;

                    { Marking }

                    if msqc > 0 then
                      begin
                        if (mbrc > 0) or ((mbrc = 0) and (mbfc = 0)) then
                          MoveFlagSet(moves[i0], mfandf);
                        if mbfc > 0 then
                          MoveFlagSet(moves[i0], mfandr)
                      end
                  end
              end
          end
      end
  end; { PosMarkDisambiguation }

  procedure PosMarkNotation(var pos: postype; var gms: gmstype);
    var
      index: Integer;
  begin
    PosMarkChecks(pos, gms);
    PosMarkCheckmates(pos, gms);
    PosMarkDisambiguation(pos, gms);
    with gms do
      for index := 0 to movecount - 1 do
        MoveFlagSet(moves[index], mfnote)
  end; { PosMarkNotation }

  procedure PosMarkDraws(var pos: postype; var gms: gmstype);
    var
      index: Integer;

    procedure AssignDraw(mf: mftype);
    begin
      with gms do
        begin
          MoveFlagSet(moves[index], mf);
          MoveFlagSet(moves[index], mfdraw);
          MoveSetCertain(moves[index], sveven)
        end
    end; { AssignDrawFlag }

  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        begin
          if not MoveFlagTest(moves[index], mfcert) then
            begin
              PosExecute(pos, moves[index]);
              case PosCalcGt(pos) of
                gtfiftymoves:   AssignDraw(mfdrfm);
                gtinsufficient: AssignDraw(mfdrim);
                gtrepetition:   AssignDraw(mfdrrp);
                gtstalemate:    AssignDraw(mfdrsm);
                gtunterminated:
              end; { case }
              PosRetract(pos)
            end
        end
  end; { PosMarkDraws }

  function PosIsMateIn1(var pos: postype): Boolean;
    var
      myresult: Boolean;
      gms: gmstype;
      index: Integer;
  begin
    with pos, gms do
      begin
        myresult := False;
        PosGenOnlyChecks(pos, gms);
        index := 0;
        while not myresult and (index < movecount) do
          begin
            PosExecute(pos, moves[index]);
            if PosIsCheckmate(pos) then
              myresult := True;
            PosRetract(pos);
            Inc(index)
          end
      end;
    PosIsMateIn1 := myresult
  end; { PosIsMateIn1 }

  function PosIsLoseIn1(var pos: postype): Boolean;
    var
      myresult: Boolean;
      gms: gmstype;
      index: Integer;
  begin
    with pos, gms do
      begin
        PosGenerate(pos, gms);
        if movecount = 0 then
          myresult := inch
        else
          begin
            myresult := True;
            index := 0;
            while myresult and (index < movecount) do
              begin
                PosExecute(pos, moves[index]);
                if not PosIsMateIn1(pos) then
                  myresult := False;
                PosRetract(pos);
                Inc(index)
              end
          end
      end;
    PosIsLoseIn1 := myresult
  end; { PosIsLoseIn1 }

  function PosIsMateIn2(var pos: postype): Boolean;
    var
      myresult: Boolean;
      gms: gmstype;
      index: Integer;
  begin
    with pos, gms do
      begin
        myresult := False;
        index := 0;
        PosGenerate(pos, gms);
        PosMarkChecks(pos, gms);
        GmsMoveChecksToFront(gms);
        while not myresult and (index < movecount) do
          begin
            PosExecute(pos, moves[index]);
            if PosIsLoseIn1(pos) then
              myresult := True;
            PosRetract(pos);
            Inc(index)
          end
      end;
    PosIsMateIn2 := myresult
  end; { PosIsMateIn2 }

  function PosIsLoseIn2(var pos: postype): Boolean;
    var
      myresult: Boolean;
      gms: gmstype;
      index: Integer;
  begin
    with pos, gms do
      begin
        PosGenerate(pos, gms);
        if movecount = 0 then
          myresult := inch
        else
          begin
            myresult := True;
            index := 0;
            while myresult and (index < movecount) do
              begin
                PosExecute(pos, moves[index]);
                if not PosIsMateIn2(pos) then
                  myresult := False;
                PosRetract(pos);
                Inc(index)
              end
          end
      end;
    PosIsLoseIn2 := myresult
  end; { PosIsLoseIn2 }

  function PosIsMateIn3(var pos: postype): Boolean;
    var
      myresult: Boolean;
      gms: gmstype;
      index: Integer;
  begin
    with pos, gms do
      begin
        myresult := False;
        index := 0;
        PosGenerate(pos, gms);
        PosMarkChecks(pos, gms);
        GmsMoveChecksToFront(gms);
        while not myresult and (index < movecount) do
          begin
            PosExecute(pos, moves[index]);
            if PosIsLoseIn2(pos) then
              myresult := True;
            PosRetract(pos);
            Inc(index)
          end
      end;
    PosIsMateIn3 := myresult
  end; { PosIsMateIn3 }

  procedure PosMarkLoseIn1(var pos: postype; var gms: gmstype);
    var
      index: Integer;
  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        if not MoveflagTest(moves[index], mfcert) then
          begin
            PosExecute(pos, moves[index]);
            if PosIsMateIn1(pos) then
              MoveSetCertain(moves[index], svlosein1);
            PosRetract(pos)
          end
  end; { PosMarkLoseIn1 }

  procedure PosMarkMateIn2(var pos: postype; var gms: gmstype);
    var
      index: Integer;
  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        if not MoveflagTest(moves[index], mfcert) then
          begin
            PosExecute(pos, moves[index]);
            if PosIsLoseIn1(pos) then
              MoveSetCertain(moves[index], svmatein2);
            PosRetract(pos)
          end
  end; { PosMarkMateIn2 }

  procedure PosMarkLoseIn2(var pos: postype; var gms: gmstype);
    var
      index: Integer;
  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        if not MoveflagTest(moves[index], mfcert) then
          begin
            PosExecute(pos, moves[index]);
            if PosIsMateIn2(pos) then
              MoveSetCertain(moves[index], svlosein2);
            PosRetract(pos)
          end
  end; { PosMarkLoseIn2 }

  procedure PosMarkMateIn3(var pos: postype; var gms: gmstype);
    var
      index: Integer;
  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        if not MoveflagTest(moves[index], mfcert) then
          begin
            PosExecute(pos, moves[index]);
            if PosIsLoseIn2(pos) then
              MoveSetCertain(moves[index], svmatein3);
            PosRetract(pos)
          end
  end; { PosMarkMateIn3 }

  function TbWranglerProbe(var tbwrangler: tbwranglertype; var pos: postype): svtype; forward;

  procedure PosMarkTablebase(var pos: postype; var gms: gmstype; var tbwrangler: tbwranglertype);
    var
      index: Integer;
      sv: svtype;
  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        if not MoveflagTest(moves[index], mfcert) then
          begin
            PosExecute(pos, moves[index]);
            sv := TbWranglerProbe(tbwrangler, pos);
            if not IsSvBroken(sv) then
              begin
                MoveFlagSet(moves[index], mftbas);
                MoveSetCertain(moves[index], CalcSvUp(sv))
              end;
            PosRetract(pos)
          end
  end; { PosMarkTablebase }

  function PosIsResignable(var pos: postype): Boolean;
  begin
    PosIsResignable := PosIsLoseIn2(pos)
  end; { PosIsResignable }

  function PosIsResignableAfterMove(var pos: postype; var move: movetype): Boolean;
    var
      myresult: Boolean;
  begin
    PosExecute(pos, move);
    myresult := PosIsMateIn2(pos);
    PosRetract(pos);
    PosIsResignableAfterMove := myresult
  end; { PosIsResignableAfterMove }

  procedure PosMetaGenNotated(var pos: postype; var gms: gmstype);
  begin
    PosGenerate(pos, gms);
    PosMarkNotation(pos, gms)
  end; { PosMetaGenNotated }

  procedure PosMetaGenCanonical(var pos: postype; var gms: gmstype);
  begin
    PosMetaGenNotated(pos, gms);
    GmsSortBySan(gms)
  end; { PosMetaGenCanonical }

  procedure PosMetaGenDeluxe(var pos: postype; var gms: gmstype);
  begin
    PosMetaGenCanonical(pos, gms);
    PosMarkDraws(pos, gms)
  end; { PosMetaGenDeluxe }

  procedure PosMetaGenSuperDeluxe(var pos: postype; var gms: gmstype);
  begin
    PosMetaGenDeluxe(pos, gms);
    PosMarkLoseIn1(pos, gms);
    PosMarkMateIn2(pos, gms)
  end; { PosMetaGenSuperDeluxe }

  procedure PosMetaGenHyperDeluxe(var pos: postype; var gms: gmstype; var tbwrangler: tbwranglertype);
  begin
    PosMetaGenSuperDeluxe(pos, gms);
    PosMarkLoseIn2(pos, gms);
    PosMarkMateIn3(pos, gms);
    PosMarkTablebase(pos, gms, tbwrangler)
  end; { PosMetaGenHyperDeluxe }

  procedure PosMoveNotate(var pos: postype; var move: movetype);
    var
      gms: gmstype;
      foundmove: movetype;

    procedure JamFlag(mf: mftype);
      var
        f0, f1: Boolean;
    begin
      f0 := MoveFlagTest(foundmove, mf);
      f1 := MoveFlagTest(move, mf);
      if f0 <> f1 then
        if f0 then
          MoveFlagSet(move, mf)
        else
          MoveFlagReset(move, mf)
    end; { JamFlag }

  begin
    if not MoveFlagTest(move, mfnote) then
      begin
        PosMetaGenNotated(pos, gms);
        foundmove := gms.moves[GmsLocateMoveNoFail(gms, move)];
        JamFlag(mfandf);
        JamFlag(mfandr);
        JamFlag(mfchck);
        JamFlag(mfchmt);
        MoveFlagSet(move, mfnote)
      end
  end; { PosMoveNotate }

  function PosMoveDecode(var pos: postype; var move: movetype; str: String): Boolean;
    var
      myresult: Boolean;
      gms: gmstype;
      index: Integer;
  begin
    myresult := False;
    index := 0;
    move := voidmove;
    PosMetaGenNotated(pos, gms);
    with gms do
      while not myresult and (index < movecount) do
        if str = MoveEncode(moves[index]) then
          begin
            move := moves[index];
            myresult := True
          end
        else
          Inc(index);
    PosMoveDecode := myresult
  end; { PosMoveDecode }

  function PosIsValidMoveTokenList(var pos: postype; var tokenlist: tokenlisttype): Boolean;
    var
      myresult: Boolean;
      count: ecounttype;
      tokenptr: tokenptrtype;
      move: movetype;
  begin
    myresult := True;
    count := 0;
    tokenptr := tokenlist.head;
    while myresult and (tokenptr <> nil) do
      if not PosMoveDecode(pos, move, tokenptr^.tstr) then
        myresult := False
      else
        begin
          PosExecute(pos, move);
          Inc(count);
          tokenptr := tokenptr^.next
        end;
    while count > 0 do
      begin
        PosRetract(pos);
        Dec(count)
      end;
    PosIsValidMoveTokenList := myresult
  end; { PosIsValidMoveTokenList }

  function PosPerftBulk(var pos: postype; var ofile: Text; mydepth: Integer; dflag: Boolean): nctype;
    var
      ply: plytype;
      depth: Integer;

    function PosPerftBulkAux: nctype;
      var
        myresult, subsum: nctype;
        p0flag: Boolean;
        index: Integer;
        gms: gmstype;
    begin
      if depth = 0 then
        myresult := 1
      else
        begin
          p0flag := ply = 0;
          if (depth = 1) and not p0flag then
            myresult := PosCountMoves(pos)
          else

            { Calculate via recursion }

            with gms do
              begin
                myresult := 0;
                if p0flag then
                  PosMetaGenCanonical(pos, gms)
                else
                  PosGenerate(pos, gms);
                Inc(ply);
                Dec(depth);
                for index := 0 to movecount - 1 do
                  begin
                    PosExecute(pos, moves[index]);
                    subsum := PosPerftBulkAux();
                    PosRetract(pos);
                    if p0flag and dflag then
                      WriteStrNL(ofile, MoveEncode(moves[index]) + ' ' + EncodeUi64Type(subsum));
                    myresult := myresult + subsum
                  end;
                Inc(depth);
                Dec(ply)
              end

        end;
      PosPerftBulkAux := myresult
    end; { PosPerftBulkAux }

  begin
    ply := 0;
    depth := mydepth;
    PosPerftBulk := PosPerftBulkAux
  end; { PosPerftBulk }

  function PosPerftFull(var pos: postype; var ofile: Text; mydepth: Integer; dflag: Boolean): nctype;
    var
      ply: plytype;
      depth: Integer;

    function PosPerftFullAux: nctype;
      var
        myresult, subsum: nctype;
        p0flag: Boolean;
        index: Integer;
        gms: gmstype;
    begin
      if depth = 0 then
        myresult := 1
      else
        begin

          { Calculate via recursion }

          p0flag := ply = 0;
          with gms do
            begin
              myresult := 0;
              if p0flag then
                PosMetaGenCanonical(pos, gms)
              else
                PosGenerate(pos, gms);
              Inc(ply);
              Dec(depth);
              for index := 0 to movecount - 1 do
                begin
                  PosExecute(pos, moves[index]);
                  subsum := PosPerftFullAux();
                  PosRetract(pos);
                  if p0flag and dflag then
                    WriteStrNL(ofile, MoveEncode(moves[index]) + ' ' + EncodeUi64Type(subsum));
                  myresult := myresult + subsum
                end;
              Inc(depth);
              Dec(ply)
            end

        end;
      PosPerftFullAux := myresult
    end; { PosPerftFullAux }

  begin
    ply := 0;
    depth := mydepth;
    PosPerftFull := PosPerftFullAux
  end; { PosPerftFull }

  function PosPerftTran(var pos: postype; var ofile: Text; mydepth: Integer; dflag: Boolean): nctype;
    var
      myresult: nctype;
      ply: plytype;
      depth: Integer;
      ttprftptr: ttprftptrtype;
      ttprftindex: ttprftindextype;
      sigmask: ui64type;

    function PosPerftTranAux: nctype;
      var
        myresult, subsum: nctype;
        p0flag: Boolean;
        index: Integer;
        gms: gmstype;
        entryindex0, entryindex1, updateindex: ttprftindextype;
        possignature: ttprftsigtype;
    begin
      if depth = 0 then myresult := 1
      else
        begin
          p0flag := ply = 0;
          if (depth = 1) and not p0flag then
            myresult := PosCountMoves(pos)
          else
            begin

              { Calculate the position signature }

              with possignature do
                begin
                  sigword0 := (pos.mphc.bits0 and sigmask) or depth;
                  sigword1 := pos.mphc.bits1
                end;

              { Calculate the primary and secondary entry indexes }

              entryindex0 := pos.mphc.bits0 and ttprftmask;
              entryindex1 := entryindex0 xor 1;

              { Probe the transposititon table once or twice }

              if TtprftsigEq(ttprftptr^[entryindex0].ttprftsig, possignature) then
                myresult := ttprftptr^[entryindex0].pathcount
              else
                if TtprftsigEq(ttprftptr^[entryindex1].ttprftsig, possignature) then
                  myresult := ttprftptr^[entryindex1].pathcount
                else
                  begin

                    { Entry not found; instead, calculate via recursion }

                    with gms do
                      begin
                        myresult := 0;
                        if p0flag then
                          PosMetaGenCanonical(pos, gms)
                        else
                          PosGenerate(pos, gms);
                        Inc(ply);
                        Dec(depth);
                        for index := 0 to movecount - 1 do
                          begin
                            PosExecute(pos, moves[index]);
                            subsum := PosPerftTranAux();
                            PosRetract(pos);
                            if p0flag and dflag then
                              WriteStrNL(ofile, MoveEncode(moves[index]) + ' ' + EncodeUi64Type(subsum));
                            myresult := myresult + subsum
                          end;
                        Inc(depth);
                        Dec(ply)
                      end;

                    { Stash result into the transposition table; overwrite lesser entry }

                    if ttprftptr^[entryindex0].pathcount < ttprftptr^[entryindex1].pathcount then
                      updateindex := entryindex0
                    else
                      updateindex := entryindex1;
                    with ttprftptr^[updateindex] do
                      begin
                        ttprftsig := possignature;
                        pathcount := myresult
                      end

                  end
            end
        end;
      PosPerftTranAux := myresult
    end; { PosPerftTranAux }

  begin
    ply := 0;
    depth := mydepth;
    sigmask := plymax;
    sigmask := not sigmask;
    New(ttprftptr);
    for ttprftindex := 0 to ttprftmask do
      with ttprftptr^[ttprftindex] do
        begin
          TtprftsigReset(ttprftsig);
          pathcount := 0
        end;
    myresult := PosPerftTranAux;
    Dispose(ttprftptr);
    PosPerftTran := myresult
  end; { PosPerftTran }

  procedure PosRandomGameSequence(var pos: postype; var prng: prngtype; noteflag: Boolean);
  var
    gms: gmstype;
  begin
    PosLoadInitialArray(pos);
    with pos, gms do
      while not PosIsGameOver(pos) do
        begin
          if noteflag then
            PosMetaGenNotated(pos, gms)
          else
            PosGenerate(pos, gms);
          PosExecute(pos, moves[PrngRandom(prng, movecount)]);
          Assert(BoardIsValid(board, good, cavs, epsq), 'PosRandomGameSequence fault')
        end
  end; { PosRandomGameSequence }

  function PosRandomGt(var pos: postype; var prng: prngtype; noteflag: Boolean): gttype;
  begin
    PosLoadInitialArray(pos);
    PosRandomGameSequence(pos, prng, noteflag);
    PosRandomGt := PosCalcGt(pos)
  end; { PosRandomGt }

  procedure PosApplyOrderAntiMobility(var pos: postype; var gms: gmstype);
    var
      index: Integer;
  begin
    with pos, gms do
      for index := 0 to movecount - 1 do
        begin
          PosExecute(pos, moves[index]);
          moves[index].sv := -PosCountMoves(pos);
          PosRetract(pos)
        end
  end; { PosApplyOrderAntiMobility }

  procedure PosApplyOrderEstimatedGain(var pos: postype; var gms: gmstype);
    var
      index: Integer;
      atkbb: bbtype;
  begin
    with pos, gms do
      begin
        atkbb := bbdb.atkbc[evil];
        for index := 0 to movecount - 1 do
          with moves[index] do
            begin
              sv := MoveBestGain(moves[index]);
              if BbTestSq(atkbb, tosq) then
                Dec(sv, (mantosv[frman] div 2))
            end
      end
  end; { PosApplyOrderEstimatedGain }

  function PosEncode(var pos: postype): fentype;
  begin
    with pos do
      PosEncode := BoardEncode(board) +
          ' ' + EncodeColor(good) + ' ' + EncodeCavs(cavs) + ' ' + EncodeSq(epsq) +
          ' ' + EncodeInteger(hmvc) + ' ' + EncodeInteger(fmvn)
  end; { PosEncode }

  function PosDecode(var pos: postype; str: String): Boolean;
    var
      myresult: Boolean;
      tokenlist: tokenlisttype;
      tokenptr: tokenptrtype;
      tokenstr: String;
      board: boardtype;
      good: colorrtype;
      cavs: castsettype;
      epsq: sqxtype;
      hmvc: hmvctype;
      fmvn: fmvntype;
  begin

    { FEN decoding }

    TokenListInit(tokenlist);
    TokenListBuild(tokenlist, str);
    myresult := tokenlist.ecount = 6;
    if myresult then
      tokenptr := tokenlist.head;

    { Board token }

    if myresult then
      begin
        tokenstr := tokenptr^.tstr;
        tokenptr := tokenptr^.next;
        if not BoardDecode(board, tokenstr) then
          myresult := False
        else
          if not BoardIsValidCensus(board) then
            myresult := False
      end;

    { Good token }

    if myresult then
      begin
        tokenstr := tokenptr^.tstr;
        tokenptr := tokenptr^.next;
        if Length(tokenstr) <> 1 then
          myresult := False
        else
          if not IsCharColor(tokenstr[1]) then
            myresult := False
          else
            begin
              good := DecodeColor(tokenstr[1]);
              if not BoardIsValidKingPlacement(board, good) then
                myresult := False
            end
      end;

    { Cavs token }

    if myresult then
      begin
        tokenstr := tokenptr^.tstr;
        tokenptr := tokenptr^.next;
        if not IsStringCavs(tokenstr) then
          myresult := False
        else
          begin
            cavs := DecodeCavs(tokenstr);
            if not BoardIsValidCastling(board, cavs) then
              myresult := False
          end
      end;

    { Epsq token }

    if myresult then
      begin
        tokenstr := tokenptr^.tstr;
        tokenptr := tokenptr^.next;
        if not IsStringSqx(tokenstr) then
          myresult := False
        else
          begin
            epsq := DecodeSqx(tokenstr);
            if not BoardIsValidEnPassant(board, good, epsq) then
              myresult := False
          end
      end;

    { Hmvc token }

    if myresult then
      begin
        tokenstr := tokenptr^.tstr;
        tokenptr := tokenptr^.next;
        if not IsStringUnsignedInteger(tokenstr) then
          myresult := False
        else
          begin
            hmvc := DecodeUnsignedInteger(tokenstr);
            if (hmvc > 0) and (epsq <> sqnil) then
              myresult := False
          end
      end;

    { Fmvn token }

    if myresult then
      begin
        tokenstr := tokenptr^.tstr;
        tokenptr := tokenptr^.next;
        if not IsStringUnsignedInteger(tokenstr) then
          myresult := False
        else
          begin
            fmvn := DecodeUnsignedInteger(tokenstr);
            if fmvn < 1 then
              myresult := False
          end
      end;

    if myresult then
      PosLoadFromComponents(pos, board, good, cavs, epsq, hmvc, fmvn);
    TokenListTerm(tokenlist);
    PosDecode := myresult
  end; { PosDecode }

  procedure PosLoadFromPos(var pos, auxpos: postype);
    var
      spevptr: spevptrtype;
  begin
    PosDecode(pos, auxpos.ifen);
    spevptr := auxpos.usedspevlist.head;
    while spevptr <> nil do
      begin
        PosExecute(pos, spevptr^.spevmove);
        spevptr := spevptr^.next
      end
  end; { PosLoadFromPos }

  function PosPerftTask(ptr: Pointer): PtrInt;
    var
      perftblockptr: perftblockptrtype;
      pos: postype;

    function PosPerftSimpleFull(depth: Integer): nctype;
      var
        myresult: nctype;
        gms: gmstype;
        index: Integer;
    begin
      if depth = 0 then
        myresult := 1
      else
        begin
          myresult := 0;
          PosGenerate(pos, gms);
          with gms do
            for index := 0 to movecount - 1 do
              begin
                PosExecute(pos, moves[index]);
                Inc(myresult, PosPerftSimpleFull(depth - 1));
                PosRetract(pos)
              end
        end;
      PosPerftSimpleFull := myresult
    end; { PosPerftSimpleFull }

  begin
    perftblockptr := ptr;
    with perftblockptr^ do
      begin
        PosInit(pos);
        PosDecode(pos, ifen);
        mpcount := PosPerftSimpleFull(draft);
        PosTerm(pos);
        completed := True
      end;
    PosPerftTask := 0
  end; { PosPerftTask }

  function PosPerftTaskDriver(var pos: postype; limit: Integer; printflag: Boolean): nctype;
    var
      myresult: nctype;
      corecount, activecount: Integer;
      moveindex: Integer;
      gms: gmstype;
      completedcount: Integer;
      nextmoveindex: Integer;
      coreindex: Integer;
      activevec: array [coretype] of Integer;
      blocks: array [gentype] of perftblocktype;

    function FindFirstFree: Integer;
      var
        myresult: Integer;
        coreindex: Integer;
    begin
      myresult := -1;
      coreindex := 0;
      while (myresult < 0) and (coreindex < corecount) do
        if activevec[coreindex] < 0 then
          myresult := coreindex
        else
          Inc(coreindex);
      FindFirstFree := myresult
    end; { FindFirstFree }

    function FindFirstCompleted: Integer;
      var
        myresult: Integer;
        coreindex: Integer;
    begin
      myresult := -1;
      coreindex := 0;
      while (myresult < 0) and (coreindex < corecount) do
        if (activevec[coreindex] >= 0) and blocks[activevec[coreindex]].completed then
          myresult := coreindex
        else
          Inc(coreindex);
      FindFirstCompleted := myresult
    end; { FindFirstCompleted }

    procedure Dispatch(moveindex: Integer);
    begin
      activevec[FindFirstFree] := moveindex;
      blocks[moveindex].threadid := BeginThread(@PosPerftTask, @blocks[moveindex]);
      Inc(activecount)
    end; { Dispatch }

    procedure Reclaim(coreindex: Integer);
    begin
      WaitForThreadTerminate(blocks[activevec[coreindex]].threadid, 0);
      activevec[coreindex] := -1;
      Dec(activecount)
    end; { Reclaim }

  begin

    { Initialize counts and moves }

    myresult := 0;
    corecount := CalcCoreCount;
    activecount := 0;
    completedcount := 0;
    PosMetaGenCanonical(pos, gms);

    { Initialize the active core vector }

    for coreindex := 0 to corecount - 1 do
      activevec[coreindex] := -1;

    { Initialize the thread parameter blocks }

    for moveindex := 0 to gms.movecount - 1 do
      begin
        PosExecute(pos, gms.moves[moveindex]);
        with blocks[moveindex] do
          begin
            threadid := TThreadID(0);
            ifen := PosEncode(pos);
            draft := limit - 1;
            prior := MoveEncode(gms.moves[moveindex]);
            mpcount := 0;
            completed := False
          end;
        PosRetract(pos)
      end;

    { Cycle }

    nextmoveindex := 0;
    while completedcount < gms.movecount do
      if (nextmoveindex < gms.movecount) and (activecount < corecount) then
        begin
          Dispatch(nextmoveindex);
          Inc(nextmoveindex)
        end
      else
        begin
          coreindex := FindFirstCompleted;
          if coreindex >= 0 then
            begin
              Reclaim(coreindex);
              Inc(completedcount)
            end
          else
            RatNap
        end;

    { Scan/print results }

    for moveindex := 0 to gms.movecount - 1 do
      with blocks[moveindex] do
        begin
          if printflag then
            WriteStrNL(Output, prior + ' ' + EncodeUi64Type(mpcount));
          Inc(myresult, mpcount)
        end;

    { Assign final result and exit }

    PosPerftTaskDriver := myresult
  end; { PosPerftTaskDriver }

  { ***** Pawn structure routines ***** }

  procedure PawnStructReset(var pawnstruct: pawnstructtype);
    var
      color: colorrtype;
  begin
    with pawnstruct do
      for color := colorrmin to colorrmax do
        begin
          BbReset(backward[color]);
          BbReset(connected[color]);
          BbReset(isolated[color]);
          BbReset(location[color]);
          BbReset(majority[color]);
          BbReset(multiple[color]);
          BbReset(passed[color])
        end
  end; { PawnStructReset }

  procedure PawnStructLoadFromPos(var pawnstruct: pawnstructtype; var pos: postype);
    var
      color: colorrtype;
      c0bb, c1bb: bbtype;
      m0bb, m1bb: bbtype;
      bb: bbtype;
      sq: sqxtype;
      advdir: dirtype;
      advsq: sqxtype;
      countbb: bbtype;
  begin
    with pawnstruct, pos, bbdb do
      begin
        PawnStructReset(pawnstruct);
        for color := colorrmin to colorrmax do
          begin

            { Setup }

            c0bb := locbm[synthpawn[color]];
            c1bb := locbm[synthpawn[othercolor[color]]];
            advdir := pawnadvdir[color];

            { Scan }

            bb := c0bb;
            repeat
              sq := BbNextSq(bb);
              if sq <> sqnil then
                begin

                  { Backward }

                  if BbNI2(c0bb, guardedbbvec[color, sq]) then
                    begin
                      advsq := advance[sq, advdir];
                      if advsq <> sqnil then
                        if not BbNI2(c1bb, pawnatkbbvec[color, advsq]) then
                          BbSetSq(backward[color], sq)
                    end;

                  { Connected }

                  if not BbNI2(c0bb, connectbbvec[sq]) then
                    BbSetSq(connected[color], sq);

                  { Isolated }

                  if BbNI2(c0bb, adjfilebbvec[sq]) then
                    BbSetSq(isolated[color], sq);

                  { Location }

                  location[color] := c0bb;

                  { Majority }

                  BbAnd2(m0bb, c0bb, majfilebbvec[sq]);
                  BbAnd2(m1bb, c1bb, majfilebbvec[sq]);
                  if BbCount(m0bb) > BbCount(m1bb) then
                    BbSetSq(majority[color], sq);

                  { Multiple }

                  BbAnd2(countbb, c0bb, bfilebbvec[sqtobfile[sq]]);
                  if BbCount(countbb) > 1 then
                    BbSetSq(multiple[color], sq);

                  { Passed }

                  if BbNI2(c1bb, passerbbvec[color, sq]) then
                    BbSetSq(passed[color], sq)

                end
            until sq = sqnil;
          end
      end
  end; { PawnStructLoadFromPos }

  function PawnStructEncode(var pawnstruct: pawnstructtype): String;
    var
      myresult: String;
      color: colorrtype;
  begin
    with pawnstruct do
      begin
        myresult := '';
        for color := colorrmin to colorrmax do
          myresult := myresult +
              'Backward  (' + colornames[color] + '): ' + BbEncodeSqs(backward[color])  + asciinl;
        for color := colorrmin to colorrmax do
          myresult := myresult +
              'Connected (' + colornames[color] + '): ' + BbEncodeSqs(connected[color]) + asciinl;
        for color := colorrmin to colorrmax do
          myresult := myresult +
              'Isolated  (' + colornames[color] + '): ' + BbEncodeSqs(isolated[color])  + asciinl;
        for color := colorrmin to colorrmax do
          myresult := myresult +
              'Location  (' + colornames[color] + '): ' + BbEncodeSqs(location[color])  + asciinl;
        for color := colorrmin to colorrmax do
          myresult := myresult +
              'Majority  (' + colornames[color] + '): ' + BbEncodeSqs(majority[color])  + asciinl;
        for color := colorrmin to colorrmax do
          myresult := myresult +
              'Multiple  (' + colornames[color] + '): ' + BbEncodeSqs(multiple[color])  + asciinl;
        for color := colorrmin to colorrmax do
          myresult := myresult +
              'Passed    (' + colornames[color] + '): ' + BbEncodeSqs(passed[color])    + asciinl
      end;
    PawnStructEncode := myresult
  end; { PawnStructEncode }

  { ***** Evaluation transposition table routines ***** }

  procedure TTEvalReset(var tteval: ttevaltype);
    var
      ttevalindex: ttevalindextype;
  begin
    for ttevalindex := 0 to ttevalmask do
      with tteval[ttevalindex] do
        begin
          HashReset(hash);
          score := svbroken;
          flagdata := 0;
        end
  end; { TTEvalReset }

  function TTEvalNew: ttevalptrtype;
    var
      myresult: ttevalptrtype;
  begin
    New(myresult);
    TTEvalReset(myresult^);
    TTEvalNew := myresult
  end; { TTEvalNew }

  procedure TTEvalDispose(ttevalptr: ttevalptrtype);
  begin
    Dispose(ttevalptr)
  end; { TTEvalDispose }

  procedure TTEvalFetchScore(var tteval: ttevaltype; var pos: postype; var sv: svtype);
    var
      ttevalindex: ttevalindextype;
  begin
    ttevalindex := pos.mphc.bits0 and ttevalmask;
    with tteval[ttevalindex] do
      if HashEq(hash, pos.mphc) and Odd(flagdata) and (((flagdata shr 1) and 1) = pos.good) then
        sv := score
      else
        sv := svbroken
  end; { TTEvalFetchScore }

  procedure TTEvalStashScore(var tteval: ttevaltype; var pos: postype; sv: svtype);
    var
      ttevalindex: ttevalindextype;
  begin
    ttevalindex := pos.mphc.bits0 and ttevalmask;
    with tteval[ttevalindex] do
      begin
        hash := pos.mphc;
        score := sv;
        flagdata := 1 or (pos.good shl 1)
      end
  end; { TTEvalStashScore }

  { ***** Main transposition table routines ***** }

  procedure TTMainReset(var ttmain: ttmaintype);
    var
      ttmainindex: ttmainindextype;
  begin
    for ttmainindex := 0 to ttmainmask do
      with ttmain[ttmainindex] do
        begin
          HashReset(hash);
          score := svbroken;
          draft := -128;
          flagdata := 0;
          movedata := 0
        end
  end; { TTMainReset }

  function TTMainNew: ttmainptrtype;
    var
      myresult: ttmainptrtype;
  begin
    New(myresult);
    TTMainReset(myresult^);
    TTMainNew := myresult
  end; { TTMainNew }

  procedure TTMainDispose(ttmainptr: ttmainptrtype);
  begin
    Dispose(ttmainptr)
  end; { TTMainDispose }

  procedure TTMainFetchHintMove(var ttmain: ttmaintype; var pos: postype; var move: movetype);
    var
      ttmainindex: ttmainindextype;
  begin
    ttmainindex := pos.mphc.bits0 and ttmainmask;
    with ttmain[ttmainindex] do
      if HashEq(hash, pos.mphc) and Odd(flagdata) and (((flagdata shr 1) and 1) = pos.good) then
        with move do
          begin
            frsq := movedata and 63;
            tosq := (movedata shr 6) and 63;
            frman := pos.board.sqv[frsq];
            toman := pos.board.sqv[tosq];
            msc := (movedata shr 12) and 7;
            mfset := [];
            sv := svbroken
          end
      else
        move := voidmove
  end; { TTMainFetchHintMove }

  procedure TTMainStashHintMove(var ttmain: ttmaintype; var pos: postype; var move: movetype);
    var
      ttmainindex: ttmainindextype;
  begin
    ttmainindex := pos.mphc.bits0 and ttmainmask;
    with ttmain[ttmainindex] do
      begin
        hash := pos.mphc;
        score := svbroken;
        draft := -128;
        flagdata := 1 or (pos.good shl 1);
        movedata := move.frsq or (move.tosq shl 6) or (move.msc shl 12)
      end
  end; { TTMainStashHintMove }

  { ***** Pawn transposition table routines ***** }

  procedure TTPawnReset(var ttpawn: ttpawntype);
    var
      ttpawnindex: ttpawnindextype;
  begin
    for ttpawnindex := 0 to ttpawnmask do
      with ttpawn[ttpawnindex] do
        begin
          HashReset(hash);
          PawnStructReset(pawnstruct);
          score := svbroken;
          flagdata := 0
        end
  end; { TTPawnReset }

  function TTPawnNew: ttpawnptrtype;
    var
      myresult: ttpawnptrtype;
  begin
    New(myresult);
    TTPawnReset(myresult^);
    TTPawnNew := myresult
  end; { TTPawnNew }

  procedure TTPawnDispose(ttpawnptr: ttpawnptrtype);
  begin
    Dispose(ttpawnptr)
  end; { TTPawnDispose }

  procedure TTPawnFetchEntry(
      var ttpawn: ttpawntype; var pos: postype; var sv: svtype; var mypawnstruct: pawnstructtype);
    var
      ttpawnindex: ttpawnindextype;
  begin
    ttpawnindex := pos.pshc.bits0 and ttpawnmask;
    with ttpawn[ttpawnindex] do
      if HashEq(hash, pos.pshc) and
          BbEqual(pawnstruct.location[colorw], pos.bbdb.locbm[manwp]) and
          BbEqual(pawnstruct.location[colorb], pos.bbdb.locbm[manbp]) and
          Odd(flagdata) and (((flagdata shr 1) and 1) = pos.good) then
        begin
          sv := score;
          mypawnstruct := pawnstruct
        end
      else
        sv := svbroken
  end; { TTPawnFetchEntry }

  procedure TTPawnStashEntry(
      var ttpawn: ttpawntype; var pos: postype; sv: svtype; var mypawnstruct: pawnstructtype);
    var
      ttpawnindex: ttpawnindextype;
  begin
    ttpawnindex := pos.pshc.bits0 and ttpawnmask;
    with ttpawn[ttpawnindex] do
      begin
        hash := pos.pshc;
        pawnstruct := mypawnstruct;
        score := sv;
        flagdata := 1 or (pos.good shl 1)
      end
  end; { TTPawnStashEntry }

  { ***** Tablebase transposition table routines ***** }

  procedure TTTbasReset(var tttbas: tttbastype);
    var
      tttbasindex: tttbasindextype;
  begin
    for tttbasindex := 0 to tttbasmask do
      with tttbas[tttbasindex] do
        begin
          HashReset(hash);
          score := svbroken;
          flagdata := 0
        end
  end; { TTTbasReset }

  function TTTbasNew: tttbasptrtype;
    var
      myresult: tttbasptrtype;
  begin
    New(myresult);
    TTTbasReset(myresult^);
    TTTbasNew := myresult
  end; { TTTbasNew }

  procedure TTTbasDispose(tttbasptr: tttbasptrtype);
  begin
    Dispose(tttbasptr)
  end; { TTTbasDispose }

  procedure TTTbasFetchScore(var tttbas: tttbastype; var pos: postype; var sv: svtype);
    var
      tttbasindex: tttbasindextype;
  begin
    tttbasindex := pos.mphc.bits0 and tttbasmask;
    with tttbas[tttbasindex] do
      if HashEq(hash, pos.mphc) and Odd(flagdata) and (((flagdata shr 1) and 1) = pos.good) then
        sv := score
      else
        sv := svbroken
  end; { TTTbasFetchScore }

  procedure TTTbasStashScore(var tttbas: tttbastype; var pos: postype; sv: svtype);
    var
      tttbasindex: tttbasindextype;
  begin
    tttbasindex := pos.mphc.bits0 and tttbasmask;
    with tttbas[tttbasindex] do
      begin
        hash := pos.mphc;
        score := sv;
        flagdata := 1 or (pos.good shl 1)
      end
  end; { TTTbasStashScore }

  { ***** Tablebase slot vector routines ***** }

  procedure TbSlotVecReset(var tbslotvec: tbslotvectype);
    var
      tbslot: tbslottype;
  begin
    for tbslot := tbslotmin to tbslotmax do
      tbslotvec[tbslot] := sqnil
  end; { TbSlotVecReset }

  function TbSlotVecEncode(var tbslotvec: tbslotvectype): String;
    var
      myresult: String;
      tbslot: tbslottype;
      sq: sqxtype;
      needspace: Boolean;
  begin
    myresult := '[';
    needspace := False;
    for tbslot := tbslotmin to tbslotmax do
      begin
        sq := tbslotvec[tbslot];
        if sq <> sqnil then
          begin
            if needspace then
              myresult := myresult + ' '
            else
              needspace := True;
            myresult := myresult + EncodeSq(sq);
          end
      end;
    myresult := myresult + ']';
    TbSlotVecEncode := myresult
  end; { TbSlotVecEncode }

  procedure TbSlotVecLoad(var tbslotvec: tbslotvectype; var pos: postype; tbc: tbctype; isrev: Boolean);
    var
      slotindex: Integer;
      color: colorrtype;
      man: manrtype;

    procedure LoadMan;
      var
        bb: bbtype;
        sq: sqxtype;
    begin
      with pos.bbdb do
        begin
          if isrev then
            bb := locbm[otherman[man]]
          else
            bb := locbm[man];
          repeat
            sq := BbNextSq(bb);
            if sq <> sqnil then
              begin
                tbslotvec[slotindex] := sq;
                Inc(slotindex)
              end
          until sq = sqnil
        end
    end; { LoadMan }

    procedure Normalize;
      var
        tbslot: tbslottype;
    begin
      with tbdrvec[tbc] do
        begin
          if isrev then
            for tbslot := tbslotmin to mancount - 1 do
              tbslotvec[tbslot] := reflecty0[tbslotvec[tbslot]];
          case fold of
            fold10:
              begin
                if BbTestSq(flankbbvec[flankk], tbslotvec[foldslot]) then
                  for tbslot := tbslotmin to mancount - 1 do
                    tbslotvec[tbslot] := reflectx0[tbslotvec[tbslot]];
                if BbTestSq(homesbbvec[homesb], tbslotvec[foldslot]) then
                  for tbslot := tbslotmin to mancount - 1 do
                    tbslotvec[tbslot] := reflecty0[tbslotvec[tbslot]];
                if BbTestSq(bermudabb, tbslotvec[foldslot]) then
                  for tbslot := tbslotmin to mancount - 1 do
                    tbslotvec[tbslot] := reflectxy[tbslotvec[tbslot]]
              end;
            fold32:
              if BbTestSq(flankbbvec[flankk], tbslotvec[foldslot]) then
                for tbslot := tbslotmin to mancount - 1 do
                  tbslotvec[tbslot] := reflectx0[tbslotvec[tbslot]];
          end {case }
        end
    end; { TbSlotVecNormalize }

  begin
    TbSlotVecReset(tbslotvec);
    slotindex := 0;
    for color := colorrmin to colorrmax do
      for man := synthking[color] downto synthpawn[color] do
        if MsigCountMan(tbdrvec[tbc].msig, man) > 0 then
          LoadMan;
    Normalize
  end; { TbSlotVecLoad }

  function TbSlotVecFileIndex(var tbslotvec: tbslotvectype; tbc: tbctype): tbfsotype;
    var
      myresult: tbfsotype;
      scale: ui32type;
      tbslot: tbslottype;
  begin
    with tbdrvec[tbc] do
      begin
        myresult := 0;
        scale := 1;
        case fold of
          fold10:
            for tbslot := tbslotmin to mancount - 1 do
              if tbslot = foldslot then
                begin
                  Inc(myresult, (fold10map[tbslotvec[tbslot]] * scale));
                  scale := scale * 10
                end
              else
                begin
                  Inc(myresult, (tbslotvec[tbslot] * scale));
                  scale := scale * sqlen
                end;
          fold32:
            for tbslot := tbslotmin to mancount - 1 do
              if tbslot = foldslot then
                begin
                  Inc(myresult, (fold32map[tbslotvec[tbslot]] * scale));
                  scale := scale * (sqlen div 2)
                end
              else
                begin
                  Inc(myresult, (tbslotvec[tbslot] * scale));
                  scale := scale * sqlen
                end;
        end { case }
      end;
    TbSlotVecFileIndex := myresult
  end; { TbSlotVecFileIndex }

  { ***** Tablebase file record routines ***** }

  procedure TbFrOpen(var tbfr: tbfrtype);
  begin
    with tbfr do
      begin
        Assert(tbfptr = nil);
        Assert(not broken);
        New(tbfptr);
        Assign(tbfptr^, name);
        Reset(tbfptr^);
        if IOResult <> 0 then
          begin
            Dispose(tbfptr);
            tbfptr := nil;
            broken := True
          end
      end
  end; { TbFrOpen }

  procedure TbFrClose(var tbfr: tbfrtype);
  begin
    with tbfr do
      begin
        Assert(tbfptr <> nil);
        Assert(not broken);
        Close(tbfptr^);
        Dispose(tbfptr);
        tbfptr := nil
      end
  end; { TbFrClose }

  function TbFrIsBroken(var tbfr: tbfrtype): Boolean; inline;
  begin
    with tbfr do
      TbFrIsBroken := broken
  end; { TbFrIsBroken }

  function TbFrIsOpen(var tbfr: tbfrtype): Boolean; inline;
  begin
    with tbfr do
      TbFrIsOpen := tbfptr <> nil
  end; { TbFrIsOpen }

  function TbFrRead(var tbfr: tbfrtype; tbfso: tbfsotype): svtype;
    var
      myresult: svtype;
      tbbs: tbbstype;
  begin
    with tbfr do
      begin
        Seek(tbfptr^, tbfso);
        if IOResult <> 0 then
          begin
            myresult := svbroken;
            Dispose(tbfptr);
            tbfptr := nil;
            broken := True
          end
        else
          begin
            Read(tbfptr^, tbbs);
            if IOResult <> 0 then
              begin
                myresult := svbroken;
                Dispose(tbfptr);
                tbfptr := nil;
                broken := True
              end
            else
              myresult := TbBsToScore(tbbs)
          end
      end;
    TbFrRead := myresult
  end; { TbFrRead }

  procedure TbFrInit(var tbfr: tbfrtype; tbcms: tbcmstype);
  begin
    with tbfr do
      begin
        broken := False;
        name := tbdrvec[tbcms div colorrlen].fnvec[tbcms mod colorrlen];
        tbfptr := nil
      end
  end; { TbFrInit }

  procedure TbFrTerm(var tbfr: tbfrtype);
  begin
    if TbFrIsOpen(tbfr) then
      TbFrClose(tbfr)
  end; { TbFrTerm }

  { ***** Tablebase file record vector routines ***** }

  procedure TbFrVecInit(var tbfrvec: tbfrvectype);
    var
      tbcms: tbcmstype;
  begin
    for tbcms := tbcmsmin to tbcmsmax do
      TbFrInit(tbfrvec[tbcms], tbcms)
  end; { TbFrVecInit }

  procedure TbFrVecTerm(var tbfrvec: tbfrvectype);
    var
      tbcms: tbcmstype;
  begin
    for tbcms := tbcmsmin to tbcmsmax do
      TbFrTerm(tbfrvec[tbcms])
  end; { TbFrVecTerm }

  function TbFrVecNew: tbfrvecptrtype;
    var
      myresult: tbfrvecptrtype;
  begin
    New(myresult);
    TbFrVecInit(myresult^);
    TbFrVecNew := myresult
  end; { TbFrVecNew }

  procedure TbFrVecDispose(tbfrvecptr: tbfrvecptrtype);
  begin
    TbFrVecTerm(tbfrvecptr^);
    Dispose(tbfrvecptr)
  end; { TbFrVecDispose }

  { ***** Tablebase wrangler routines ***** }

  procedure TbWranglerInit(var tbwrangler: tbwranglertype);
  begin
    with tbwrangler do
      begin
        opencount := 0;
        replindex := 0;
        tbfrvecptr := TbFrVecNew;
        tttbasptr := TTTbasNew
      end
  end; { TbWranglerInit }

  procedure TbWranglerTerm(var tbwrangler: tbwranglertype);
  begin
    with tbwrangler do
      begin
        TbFrVecDispose(tbfrvecptr);
        TTTbasDispose(tttbasptr)
      end
  end; { TbWranglerTerm }

  function TbWranglerProbe(var tbwrangler: tbwranglertype; var pos: postype): svtype;
    var
      myresult: svtype;
      done: Boolean;
      probe: tbcmsxtype;
      tbcms: tbcmstype;
      tbc: tbctype;
      color: colorrtype;
      tbslotvec: tbslotvectype;
      seekindex: tbfsotype;

  begin
    with tbwrangler do
      begin
        done := False;

        { Probe the tablebase transposition table }

        if not done then
          if tttbasptr <> nil then
            begin
              TTTbasFetchScore(tttbasptr^, pos, myresult);
              if not IsSvBroken(myresult) then
                done := True
            end;

        { Probe the lookup signature table to locate a match }

        if not done then
          begin
            probe := PosProbeTablebaseSignatureVector(pos);
            if probe = tbcmsnil then
              begin
                myresult := svbroken;
                done := True;
              end
          end;

        { Identify the file vector index and check for broken status }

        if not done then
          begin
            tbc := tbmsmvec[probe].tbc;
            if tbmsmvec[probe].isrev then
              color := pos.evil
            else
              color := pos.good;
            tbcms := (tbc * colorrlen) + color;
            if TbFrIsBroken(tbfrvecptr^[tbcms]) then
              begin
                myresult := svbroken;
                done := True
              end
          end;

        { Ensure that the file is open }

        if not done then
          begin
            if not TbFrIsOpen(tbfrvecptr^[tbcms]) then
              begin
                while opencount = tbopenlimit do
                  begin
                    if TbFrIsOpen(tbfrvecptr^[replindex]) then
                      begin
                        TbFrClose(tbfrvecptr^[replindex]);
                        Dec(opencount)
                      end;
                    replindex := (replindex + 1) mod tbcmslen
                  end;
                TbFrOpen(tbfrvecptr^[tbcms]);
                if TbFrIsOpen(tbfrvecptr^[tbcms]) then
                  Inc(opencount)
                else
                  begin
                    myresult := svbroken;
                    done := True
                  end
              end
          end;

        { Determine the seek index and try the seek and read }

        if not done then
          begin
            TbSlotVecLoad(tbslotvec, pos, tbc, tbmsmvec[probe].isrev);
            seekindex := TbSlotVecFileIndex(tbslotvec, tbc);
            myresult := TbFrRead(tbfrvecptr^[tbcms], seekindex);
            if TbFrIsBroken(tbfrvecptr^[tbcms]) then
              begin
                Dec(opencount);
                myresult := svbroken;
                done := True
              end
            else
              if tttbasptr <> nil then
                TTTbasStashScore(tttbasptr^, pos, myresult)
          end
      end;
    TbWranglerProbe := myresult
  end; { TbWranglerProbe }

  { ***** Game termination statistics routines ***** }

  procedure GtStatsReset(var gtstats: gtstatstype);
    var
      gt: gttype;
  begin
    for gt := gtmin to gtmax do
      gtstats[gt] := 0
  end; { GtStatsReset }

  procedure GtStatsFill(var gtstats: gtstatstype; var prng: prngtype; limit: nctype);
    var
      index: nctype;
      pos: postype;
  begin
    GtStatsReset(gtstats);
    PosInit(pos);
    index := 0;
    while index < limit do
      begin
        Inc(gtstats[PosRandomGt(pos, prng, False)]);
        Inc(index)
      end;
    PosTerm(pos)
  end; { GtStatsFill }

  function GtStatsEncode(var gtstats: gtstatstype): String;
    var
      myresult: String;
      gt: gttype;
      sum: nctype;
  begin
    myresult := '';
    sum := 0;
    for gt := gtmin to gtmax do
      Inc(sum, gtstats[gt]);
    if sum > 0 then
      begin
        for gt := gtmin to gtmax do
          myresult := myresult + gtnames[gt] + ' ' + EncodeUi64Type(gtstats[gt]) + asciinl;
        myresult := myresult + 'Total ' + EncodeUi64Type(sum) + asciinl
      end;
    GtStatsEncode := myresult
  end; { GtStatsEncode }

  { ***** Variation routines ***** }

  procedure VariationReset(var variation: variationtype);
  begin
    with variation do
      begin
        MnListReset(freelist);
        MnListReset(usedlist)
      end
  end; { VariationReset }

  procedure VariationInit(var variation: variationtype);
  begin
    with variation do
      begin
        MnListInit(freelist);
        MnListInit(usedlist)
      end
  end; { VariationInit }

  procedure VariationTerm(var variation: variationtype);
  begin
    with variation do
      begin
        MnListTerm(freelist);
        MnListTerm(usedlist)
      end
  end; { VariationTerm }

  function VariationLength(var variation: variationtype): Integer;
  begin
    with variation do
      VariationLength := usedlist.ecount
  end; { VariationLength }

  procedure VariationFetchNthMove(var variation: variationtype; index: Integer; var move: movetype);
    var
      count: Integer;
      mnptr: mnptrtype;
  begin
    with variation do
      begin
        count := 0;
        mnptr := usedlist.head;
        while count < index do
          begin
            mnptr := mnptr^.next;
            Inc(count)
          end;
        move := mnptr^.move
      end
  end; { VariationFetchNthMove }

  procedure VariationRecycleTail(var variation: variationtype);
  begin
    with variation do
      MnListAppendTail(freelist, MnListDetachTail(usedlist))
  end; { VariationRecycleTail }

  procedure VariationRecycle(var variation: variationtype);
  begin
    with variation do
      while usedlist.tail <> nil do
        VariationRecycleTail(variation)
  end; { VariationRecycle }

  procedure VariationAppendMove(var variation: variationtype; var move: movetype);
    var
      mnptr: mnptrtype;
  begin
    with variation do
      begin
        if freelist.tail = nil then
          begin
            New(mnptr);
            MnListAppendTail(freelist, mnptr)
          end;
        mnptr := MnListDetachTail(freelist);
        mnptr^.move := move;
        MnListAppendTail(usedlist, mnptr)
      end
  end; { VariationAppendMove }

  procedure VariationAppend(var variation, subvariation: variationtype);
    var
      mnptr: mnptrtype;
  begin
    with variation do
      begin
        mnptr := subvariation.usedlist.head;
        while mnptr <> nil do
          begin
            VariationAppendMove(variation, mnptr^.move);
            mnptr := mnptr^.next
          end
      end
  end; { VariationAppend }

  procedure VariationAssign(var variation, altvariation: variationtype);
  begin
    VariationRecycle(variation);
    VariationAppend(variation, altvariation)
  end; { VariationAssign }

  procedure VariationBuild(
      var variation: variationtype;
      var move: movetype; var subvariation: variationtype);
  begin
    VariationRecycle(variation);
    VariationAppendMove(variation, move);
    VariationAppend(variation, subvariation)
  end; { VariationBuild }

  procedure VariationNotate(var variation: variationtype; var pos: postype);
    var
      mnptr: mnptrtype;
      count: ecounttype;
  begin
    with variation do
      begin
        count := 0;
        mnptr := usedlist.head;
        while mnptr <> nil do
          begin
            PosMoveNotate(pos, mnptr^.move);
            PosExecute(pos, mnptr^.move);
            Inc(count);
            mnptr := mnptr^.next
          end;
        while count > 0 do
          begin
            PosRetract(pos);
            Dec(count)
          end
      end
  end; { VariationNotate }

  function VariationPosEncode(var variation: variationtype; var pos: postype): String;
    var
      myresult: String;
      mnptr: mnptrtype;
      mc: mctype;
  begin
    with variation do
      begin
        myresult := '';
        VariationNotate(variation, pos);
        PosLoadToMc(pos, mc);
        mnptr := usedlist.head;
        while mnptr <> nil do
          begin
            if (mc.good = colorw) or (mnptr = usedlist.head) then
              myresult := myresult + McEncode(mc) + ' ';
            myresult := myresult + MoveEncode(mnptr^.move);
            McIncrement(mc);
            mnptr := mnptr^.next;
            if mnptr <> nil then
              myresult := myresult + ' '
          end
      end;
    VariationPosEncode := myresult
  end; { VariationPosEncode }

  { ***** PGN tag pair routines ***** }

  procedure PtpairValueSet(var ptpair: ptpairtype; mytag: String);
  begin
    with ptpair do
      begin
        tag := mytag;
        use := True
      end
  end; { PtpairValueSet }

  procedure PtpairValueReset(var ptpair: ptpairtype);
  begin
    with ptpair do
      begin
        tag := '';
        use := False
      end
  end; { PtpairValueReset }

  function PtpairEncode(var ptpair: ptpairtype): String;
  begin
    with ptpair do
      PtpairEncode := '[' + ptnnames[ptn] + ' "' + tag + '"]'
  end; { PtpairEncode }

  { ***** PGN game routines ***** }

  procedure PgnGameTagSet(var pgngame: pgngametype; ptn: ptntype; str: String);
  begin
    PtpairValueSet(pgngame.ptnvec[ptn], str)
  end; { PgnGameTagSet }

  procedure PgnGameTagReset(var pgngame: pgngametype; ptn: ptntype);
  begin
    PtpairValueReset(pgngame.ptnvec[ptn])
  end; { PgnGameTagReset }

  procedure PgnGameReset(var pgngame: pgngametype);
    var
      ptnindex: ptntype;
      myyear, mymonth, myday: ui16type;
  begin
    with pgngame do
      begin

        { Capture the date }

        DecodeDate(Date, myyear, mymonth, myday);

        { Reset all tag pairs }

        for ptnindex := ptnmin to ptnmax do
          PgnGameTagReset(pgngame, ptnindex);

        { Set required tag pairs }

        PgnGameTagSet(pgngame, ptnevent,  'Unknown event');
        PgnGameTagSet(pgngame, ptnsite,   'Unknown site');
        PgnGameTagSet(pgngame, ptndate,   Format('%.4d.%.2d.%.2d', [myyear, mymonth, myday]));
        PgnGameTagSet(pgngame, ptnround,  '-');
        PgnGameTagSet(pgngame, ptnwhite,  'Unknown player');
        PgnGameTagSet(pgngame, ptnblack,  'Unknown player');
        PgnGameTagSet(pgngame, ptnresult, grnames[grnone]);

        { Other }

        McReset(imc);
        MnListReset(mnlist);
        gr := grnone;
        ifen := startfen

      end
  end; { PgnGameReset }

  procedure PgnGameInit(var pgngame: pgngametype);
    var
      ptnindex: ptntype;
  begin
    with pgngame do
      begin
        for ptnindex := ptnmin to ptnmax do
          ptnvec[ptnindex].ptn := ptntype(ptnindex);
        MnListInit(mnlist);
        PgnGameReset(pgngame)
      end
  end; { PgnGameInit }

  procedure PgnGameTerm(var pgngame: pgngametype);
  begin
    MnListTerm(pgngame.mnlist)
  end; { PgnGameTerm }

  procedure PgnGameSetResult(var pgngame: pgngametype; mygr: grtype);
  begin
    with pgngame do
      begin
        gr := mygr;
        PtpairValueSet(ptnvec[ptnresult], grnames[gr])
      end
  end; { PgnGameSetResult }

  procedure PgnGameAddMove(var pgngame: pgngametype; var mymove: movetype);
    var
      mnptr: mnptrtype;
  begin
    with pgngame do
      begin
        New(mnptr);
        mnptr^.move := mymove;
        MnListAppendTail(mnlist, mnptr)
      end
  end; { PgnGameAddMove }

  procedure PgnGameDelMove(var pgngame: pgngametype);
    var
      mnptr: mnptrtype;
  begin
    with pgngame do
      begin
        mnptr:= MnListDetachTail(mnlist);
        Dispose(mnptr)
      end
  end; { PgnGameDelMove }

  procedure PgnGameLoadFromPos(var pgngame: pgngametype; pos: postype);
    var
      auxpos: postype;
      spevptr: spevptrtype;
  begin
    with pgngame do
      begin
        PgnGameReset(pgngame);
        PosInit(auxpos);
        PosDecode(auxpos, pos.ifen);
        PosLoadToMc(auxpos, imc);
        PosTerm(auxpos);
        ifen := pos.ifen;
        if ifen <> startfen then
          PgnGameTagSet(pgngame, ptnfen, ifen);
        spevptr := pos.usedspevlist.head;
        while spevptr <> nil do
          begin
            PgnGameAddMove(pgngame, spevptr^.spevmove);
            spevptr := spevptr^.next
          end;
        PgnGameSetResult(pgngame, PosCalcGr(pos))
      end
  end; { PgnGameLoadFromPos }

  procedure PgnGameRandom(var pgngame: pgngametype; var prng: prngtype);
    var
      pos: postype;
      myyear, mymonth, myday: ui16type;
  begin
    with pgngame do
      begin
        PosInit(pos);
        DecodeDate(Date, myyear, mymonth, myday);
        PosRandomGameSequence(pos, prng, True);
        PgnGameLoadFromPos(pgngame, pos);
        PgnGameTagSet(pgngame, ptnevent,       'Random Game');
        PgnGameTagSet(pgngame, ptndate,        Format('%.4d.%.2d.%.2d', [myyear, mymonth, myday]));
        PgnGameTagSet(pgngame, ptnwhite,       'Random player');
        PgnGameTagSet(pgngame, ptnblack,       'Random player');
        PgnGameTagSet(pgngame, ptnendfen,      PosEncode(pos));
        PgnGameTagSet(pgngame, ptntermination, gtnames[PosCalcGt(pos)]);
        PgnGameTagSet(pgngame, ptnplycount,    EncodeInteger(pos.usedspevlist.ecount));
        PosTerm(pos)
      end
  end; { PgnGameRandom }

  function PgnGameEncode(var pgngame: pgngametype): String;
    var
      myresult: String;
      ptnindex: ptntype;
      mc: mctype;
      mnptr: mnptrtype;
      move: movetype;
      column: Integer;

    procedure PwItem(str: String);
      var
        limit: Integer;
    begin
      limit := Length(str);
      if (column + 1 + limit) >= 100 then
        begin
          myresult := myresult + asciinl;
          column := 0
        end;
      if column = 0 then
        begin
          myresult := myresult + str;
          column := limit
        end
      else
        begin
          myresult := myresult + ' ' + str;
          Inc(column, (1 + limit))
        end
    end; { PwItem }

  begin
    with pgngame do
      begin
        myresult := '';

        { Initialize the move cursor }

        mc := imc;

        { Tag pairs and first separation line }

        for ptnindex := ptnmin to ptnmax do
          if ptnvec[ptnindex].use then
            myresult := myresult + PtpairEncode(ptnvec[ptnindex]) + asciinl;
        myresult := myresult + asciinl;

        { Move text, game result, and second separation line }

        column := 0;
        mnptr := mnlist.head;
        while mnptr <> nil do
          begin
            move := mnptr^.move;
            if (mnptr = mnlist.head) or (mantocolor[move.frman] = colorw) then
              PwItem(McEncode(mc));
            PwItem(MoveEncode(move));
            McIncrement(mc);
            mnptr := mnptr^.next
          end;
        PwItem(grnames[gr]);
        if column <> 0 then
          myresult := myresult + asciinl;
        myresult := myresult + asciinl
      end;
    PgnGameEncode := myresult
  end; { PgnGameEncode }

  { ***** Benchmark routine ***** }

  function Bench: nctype;
    var
      myresult: nctype;
      pos: postype;
  begin
    PosInit(pos);
    PosDecode(pos, 'r3r1k1/1ppq1ppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PPQ1PPP/R3R1K1 w - - 0 11');
    myresult := PosPerftTaskDriver(pos, 4, False);
    PosTerm(pos);
    Bench := myresult
  end; { Bench }

  { ***** Self testing routines ***** }

  function SelfTest(var ofile: Text): Boolean;
    var
      myresult: Boolean;
      stprindex: Integer;

    function TestBulkEntry: Boolean;
      var
        myresult: Boolean;
        pos: postype;
        depth: Integer;

      function TestBulkEntryDepth: Boolean;
        var
          myresult: Boolean;
          target, actual: nctype;
      begin
        with stprvec[stprindex] do
          begin
            target := tvec[depth];
            actual := PosPerftBulk(pos, ofile, depth, False);
            myresult := actual = target;
            if not myresult then
              begin
                WriteStrNL(ofile, 'FEN: ' + fen + '   depth: ' + EncodeInteger(depth));
                WriteStrNL(ofile, 'Target: ' + EncodeUi64Type(target));
                WriteStrNL(ofile, 'Actual: ' + EncodeUi64Type(actual));
                WriteStrNL(ofile, 'TestBulkEntryDepth: perft fault')
              end
          end;
        TestBulkEntryDepth := myresult
      end; { TestBulkEntryDepth }

    begin
      with stprvec[stprindex] do
        begin
          PosInit(pos);
          if not PosDecode(pos, fen) then
            begin
              WriteStrNL(ofile, 'FEN: ' + fen);
              WriteStrNL(ofile, 'TestBulkEntry: decode fault');
              myresult := False
            end
          else
            begin
              myresult := True;
              depth := stprdepthmin;
              while myresult and (depth <= stprdepthmax) do
                if TestBulkEntryDepth then
                  Inc(depth)
                else
                  myresult := False
            end;
          PosTerm(pos)
        end;
      TestBulkEntry := myresult
    end; { TestBulkEntry }

  begin
    myresult := True;
    stprindex := stprmin;
    while myresult and (stprindex <= stprmax) do
      if TestBulkEntry then
        Inc(stprindex)
      else
        myresult := False;
    SelfTest := myresult
  end; { SelfTest }

  { ***** Killers routines ***** }

  procedure KillersReset(var killers: killerstype);
  begin
    with killers do
      begin
        k0move := voidmove;
        k1move := voidmove
      end
  end; { KillersReset }

  procedure KillersAddMove(var killers: killerstype; var move: movetype);
  begin
    with killers do
      begin
        if not MoveIsSame(move, k0move) then
          begin
            k1move := k0move;
            k0move := move
          end
      end
  end; { KillersAddMove }

  { ***** Ply indexed record routines ***** }

  procedure PirClear(var pir: pirtype);
  begin
    with pir do
      begin
        isgainersonly := False;
        pms := pmsstart;
        standsv := svbroken;
        extension := 0;
        pickcount := 0;
        bestmove := voidmove;
        srchmove := voidmove;
        srchsv := svbroken;
        VariationRecycle(pv);
        GmsReset(gms)
      end
  end; { PirClear }

  procedure PirReset(var pir: pirtype);
  begin
    with pir do
      begin
        nss := nssexit;
        depth := 0;
        KillersReset(killers);
        WindowSetFullWidth(window);
        PirClear(pir)
      end
  end; { PirReset }

  procedure PirInit(var pir: pirtype; ply: plytype);
  begin
    with pir do
      begin
        isplyzero := ply = plymin;
        isplyone := ply = 1;
        islastply := ply = plymax;
        isdrawtest := ply > 1;
        ispzmover := not Odd(ply);
        VariationInit(pv);
        PirReset(pir)
      end
  end; { PirInit }

  procedure PirTerm(var pir: pirtype);
  begin
    with pir do
      VariationTerm(pv);
  end; { PirInit }

  { ***** Ply indexed record vector routines ***** }

  procedure PirVecReset(var pirvec: pirvectype);
    var
      ply: plytype;
  begin
    for ply := plymin to plymax do
      PirReset(pirvec[ply])
  end; { PirVecReset }

  procedure PirVecInit(var pirvec: pirvectype);
    var
      ply: plytype;
  begin
    for ply := plymin to plymax do
      PirInit(pirvec[ply], ply)
  end; { PirVecInit }

  procedure PirVecTerm(var pirvec: pirvectype);
    var
      ply: plytype;
  begin
    for ply := plymin to plymax do
      PirTerm(pirvec[ply])
  end; { PirVecTerm }

  { ***** Iteration indexed record routines ***** }

  procedure IirReset(var iir: iirtype);
  begin
    with iir do
      sv := svbroken
  end; { IirReset }

  procedure IirInit(var iir: iirtype);
  begin
    IirReset(iir)
  end; { IirInit }

  procedure IirTerm(var iir: iirtype);
  begin
  end; { IirTerm }

  { ***** Iteration indexed record vector routines ***** }

  procedure IirVecReset(var iirvec: iirvectype);
    var
      iter: itertype;
  begin
    for iter := itermin to itermax do
      IirReset(iirvec[iter])
  end; { IirVecReset }

  procedure IirVecInit(var iirvec: iirvectype);
    var
      iter: itertype;
  begin
    for iter := itermin to itermax do
      IirInit(iirvec[iter])
  end; { IirVecInit }

  procedure IirVecTerm(var iirvec: iirvectype);
    var
      iter: itertype;
  begin
    for iter := itermin to itermax do
      IirTerm(iirvec[iter])
  end; { IirVecTerm }

  { ***** Search resource limit routines ***** }

  procedure SrlSetNone(var srl: srltype);
  begin
    with srl do
      srlf := srlfnone
  end; { SrlSetNone }

  procedure SrlSetIter(var srl: srltype; limit: Integer);
  begin
    with srl do
      begin
        srlf := srlfiter;
        limititer := limit
      end
  end; { SrlSetIter }

  procedure SrlSetNode(var srl: srltype; limit: nctype);
  begin
    with srl do
      begin
        srlf := srlfnode;
        limitnode := limit
      end
  end; { SrlSetNode }

  procedure SrlSetFtim(var srl: srltype; limit: usectype);
  begin
    with srl do
      begin
        srlf := srlfftim;
        limitftim := limit
      end
  end; { SrlSetFtim }

  procedure SrlSetMtim(var srl: srltype; limit: usectype);
  begin
    with srl do
      begin
        srlf := srlfmtim;
        limitmtim := limit
      end
  end; { SrlSetMtim }

  { ***** EPD value node routines ***** }

  function EvnNew(str: String): evnptrtype;
    var
      evnptr: evnptrtype;
  begin
    New(evnptr);
    with evnptr^ do
      begin
        evstr := str;
        prev := nil;
        next := nil
      end;
    EvnNew := evnptr
  end; { EvnNew }

  procedure EvnDispose(evnptr: evnptrtype);
  begin
    Dispose(evnptr)
  end; { EvnDispose }

  function EvnEncode(var evn: evntype): String;
    var
      myresult: String;
  begin
    with evn do
      if IsStringQuoted(evstr) or IsStringWithSemicolon(evstr) then
        myresult := '"' + evstr + '"'
      else
        myresult := evstr;
    EvnEncode := myresult
  end; { EvnEncode }

  { ***** EPD value list routines ***** }

  procedure EvnListRelease(var evnlist: evnlisttype);
    var
      evnptr0, evnptr1: evnptrtype;
  begin
    with evnlist do
      begin
        evnptr0 := head;
        while evnptr0 <> nil do
          begin
            evnptr1 := evnptr0^.next;
            EvnDispose(evnptr0);
            evnptr0 := evnptr1
          end;
        head := nil;
        tail := nil
      end
  end; { EvnListRelease }

  { ***** EPD operation node routines ***** }

  procedure EonAppend(var eon: eontype; evnptr: evnptrtype);
  begin
    with eon, evnlist do
      begin
        if tail = nil then
          head := evnptr
        else
          begin
            tail^.next := evnptr;
            evnptr^.prev := tail
          end;
        tail := evnptr
      end
  end; { EonAppend }

  function EonNew(str: String): eonptrtype;
    var
      eonptr: eonptrtype;
  begin
    New(eonptr);
    with eonptr^ do
      begin
        eostr := str;
        evnlist.head := nil;
        evnlist.tail := nil;
        prev := nil;
        next := nil
      end;
    EonNew := eonptr
  end; { EonNew }

  procedure EonDispose(eonptr: eonptrtype);
  begin
    EvnListRelease(eonptr^.evnlist);
    Dispose(eonptr)
  end; { EonDispose }

  function EonEncode(var eon: eontype): String;
    var
      myresult: String;
      evnptr: evnptrtype;
  begin
    with eon do
      begin
        myresult := eostr;
        evnptr := evnlist.head;
        while evnptr <> nil do
          begin
            myresult := myresult + ' ' + EvnEncode(evnptr^);
            evnptr := evnptr^.next
          end;
        myresult := myresult + ';'
      end;
    EonEncode := myresult
  end; { EonEncode }

  { ***** EPD operation list routines ***** }

  procedure EonListRelease(var eonlist: eonlisttype);
    var
      eonptr0, eonptr1: eonptrtype;
  begin
    with eonlist do
      begin
        eonptr0 := head;
        while eonptr0 <> nil do
          begin
            eonptr1 := eonptr0^.next;
            EonDispose(eonptr0);
            eonptr0 := eonptr1
          end;
        head := nil;
        tail := nil
      end
  end; { EonListRelease }

  { ***** EPD whole record routines ***** }

  procedure EpdReset(var epd: epdtype);
  begin
    with epd do
      begin
        fen := startfen;
        EonListRelease(eonlist)
      end
  end; { EpdReset }

  procedure EpdInit(var epd: epdtype);
  begin
    with epd do
      begin
        eonlist.head := nil;
        eonlist.tail := nil;
        EpdReset(epd)
      end
  end; { EpdInit }

  procedure EpdTerm(var epd: epdtype);
  begin
    EonListRelease(epd.eonlist)
  end; { EpdTerm }

  procedure EpdAppend(var epd: epdtype; eonptr: eonptrtype);
  begin
    with epd, eonlist do
      begin
        if tail = nil then
          head := eonptr
        else
          begin
            tail^.next := eonptr;
            eonptr^.prev := tail
          end;
        tail := eonptr
      end
  end; { EpdAppend }

  function EpdAddEonStr(var epd: epdtype; str: String): eonptrtype;
    var
      myresult: eonptrtype;
  begin
    myresult := EonNew(str);
    EpdAppend(epd, myresult);
    EpdAddEonStr := myresult
  end; { EpdAddEonStr }

  procedure EpdAppendAcn(var epd: epdtype; acnvalue: nctype);
    var
      eonptr: eonptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'acn');
    EonAppend(eonptr^, EvnNew(EncodeUi64Type(acnvalue)))
  end; { EpdAppendAcn }

  procedure EpdAppendBm(var epd: epdtype; bmvalue: mnlisttype);
    var
      eonptr: eonptrtype;
      mnptr: mnptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'bm');
    mnptr := bmvalue.head;
    while mnptr <> nil do
      begin
        EonAppend(eonptr^, EvnNew(MoveEncode(mnptr^.move)));
        mnptr := mnptr^.next
      end
  end; { EpdAppendBm }

  procedure EpdAppendCte(var epd: epdtype; ctevalue: usectype);
    var
      comptime: comptimetype;
      eonptr: eonptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'cte');
    CompTimeLoadFromUsec(comptime, ctevalue);
    EonAppend(eonptr^, EvnNew(CompTimeEncode(comptime)))
  end; { EpdAppendCte }

  procedure EpdAppendCtcc(var epd: epdtype; ctccvalue: chessclocktype);
    var
      comptime: comptimetype;
      eonptr: eonptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'ctcc');
    ChessClockUpdate(ctccvalue);
    CompTimeLoadFromUsec(comptime, ctccvalue.timervec[colorw].current);
    EonAppend(eonptr^, EvnNew(CompTimeEncode(comptime)));
    CompTimeLoadFromUsec(comptime, ctccvalue.timervec[colorb].current);
    EonAppend(eonptr^, EvnNew(CompTimeEncode(comptime)))
  end; { EpdAppendCtcc }

  procedure EpdAppendCtu(var epd: epdtype; ctuvalue: usectype);
    var
      comptime: comptimetype;
      eonptr: eonptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'ctu');
    CompTimeLoadFromUsec(comptime, ctuvalue);
    EonAppend(eonptr^, EvnNew(CompTimeEncode(comptime)))
  end; { EpdAppendCte }

  procedure EpdAppendDm(var epd: epdtype; dmvalue: Integer);
    var
      eonptr: eonptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'dm');
    EonAppend(eonptr^, EvnNew(EncodeInteger(dmvalue)))
  end; { EpdAppendDm }

  procedure EpdAppendId(var epd: epdtype; idvalue: String);
    var
      eonptr: eonptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'id');
    EonAppend(eonptr^, EvnNew(idvalue))
  end; { EpdAppendId }

  procedure EpdAppendPes(var epd: epdtype; pesvalue: svtype);
    var
      eonptr: eonptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'pes');
    EonAppend(eonptr^, EvnNew(EncodeSv(pesvalue)))
  end; { EpdAppendPes }

  procedure EpdAppendPv(var epd: epdtype; pvvalue: mnlisttype);
    var
      eonptr: eonptrtype;
      mnptr: mnptrtype;
  begin
    eonptr := EpdAddEonStr(epd, 'pv');
    mnptr := pvvalue.head;
    while mnptr <> nil do
      begin
        EonAppend(eonptr^, EvnNew(MoveEncode(mnptr^.move)));
        mnptr := mnptr^.next
      end
  end; { EpdAppendPv }

  procedure EpdLoadFromPos(var epd: epdtype; var pos: postype);
  begin
    with epd do
      begin
        EpdReset(epd);
        fen := PosEncode(pos)
      end
  end; { EpdLoadFromPos }

  procedure EpdLoadFromSsc(var epd: epdtype; var ssc: ssctype);
  begin
    with epd, ssc do
      begin
        EpdLoadFromPos(epd, rootpos);
        EpdAppendAcn(epd, nodecount);
        EpdAppendCte(epd, TimerCurrent(ssctimer));
        EpdAppendPes(epd, predsv);
        EpdAppendPv(epd, predvar.usedlist);
        if IsSvMating(predsv) then
          EpdAppendDm(epd, CalcMatingDistance(predsv))
      end
  end; { EpdLoadFromSsc }

  function EpdEncode(var epd: epdtype): String;
    var
      myresult: String;
      eonptr: eonptrtype;
  begin
    with epd do
      begin
        myresult := fen;
        eonptr := eonlist.head;
        while eonptr <> nil do
          begin
            myresult := myresult + ' ' + EonEncode(eonptr^);
            eonptr := eonptr^.next
          end
      end;
    EpdEncode := myresult
  end; { EpdEncode }

  { ***** Selection/search context routines ***** }

  procedure SscReset(var ssc: ssctype);
  begin
    with ssc do
      begin
        TimerReset(ssctimer);
        sscoptnset := [];
        PosReset(rootpos);
        GmsReset(rootgms);
        isleftmost := False;
        WindowSetFullWidth(rootwindow);
        PosReset(currpos);
        VariationRecycle(currvar);
        {SrlSetFtim(srl, (5 * 1000000));}
        SrlSetNode(srl, 1000000);
        VariationRecycle(priorpv);
        predsv := svbroken;
        VariationRecycle(predvar);
        nodecount := 0;
        usedusec := 0;
        st := stunterminated;
        PirVecReset(pirvec);
        IirVecReset(iirvec)
      end
  end; { SscReset }

  procedure SscInit(var ssc: ssctype);
  begin
    with ssc do
      begin
        PosInit(rootpos);
        PosInit(currpos);
        VariationInit(currvar);
        VariationInit(priorpv);
        VariationInit(predvar);
        PirVecInit(pirvec);
        IirVecInit(iirvec);
        ttevalptr := TTEvalNew;
        ttmainptr := TTMainNew;
        ttpawnptr := TTPawnNew;
        TbWranglerInit(tbwrangler);
        SscReset(ssc)
      end
  end; { SscInit }

  procedure SscTerm(var ssc: ssctype);
  begin
    with ssc do
      begin
        PosTerm(rootpos);
        PosTerm(currpos);
        VariationTerm(currvar);
        VariationTerm(priorpv);
        VariationTerm(predvar);
        PirVecTerm(pirvec);
        IirVecTerm(iirvec);
        TTEvalDispose(ttevalptr);
        TTMainDispose(ttmainptr);
        TTPawnDispose(ttpawnptr);
        TbWranglerTerm(tbwrangler)
      end
  end; { SscTerm }

  procedure SscStop(var ssc: ssctype; myst: sttype); inline;
  begin
    with ssc do
      st := myst;
  end; { SscStop }

  function SscIsGoing(var ssc: ssctype): Boolean; inline;
  begin
    with ssc do
      SscIsGoing := st = stunterminated
  end; { SscIsGoing }

  function SscIsStopped(var ssc: ssctype): Boolean; inline;
  begin
    with ssc do
      SscIsStopped := st <> stunterminated
  end; { SscIsStopped }

  procedure SscTraceCV(var ssc: ssctype);
  begin
    with ssc do
      begin
        WritePrefix(tracefile, 'cv');
        WriteStrNL(tracefile, VariationPosEncode(currvar, rootpos))
      end
  end; { SscTraceCV }

  procedure SscTraceEA(var ssc: ssctype);
    var
      epd: epdtype;
  begin
    with ssc do
      begin
        EpdInit(epd);
        EpdLoadFromSsc(epd, ssc);
        WritePrefix(tracefile, 'ea');
        WriteStrNL(tracefile, EpdEncode(epd));
        EpdTerm(epd)
      end
  end; { SscTraceEA }

  procedure SscTraceFD(var ssc: ssctype);
  begin
    with ssc do
      begin
        WritePrefix(tracefile, 'fd');
        WriteStrNL(tracefile, VariationPosEncode(currvar, rootpos))
      end
  end; { SscTraceFD }

  procedure SscTraceFV(var ssc: ssctype);
  begin
    with ssc do
      begin
        WritePrefix(tracefile, 'fv');
        WriteStr(tracefile, VariationPosEncode(predvar, rootpos));
        WriteStrNL(tracefile, '   score: ' + EncodeSv(predsv));
      end
  end; { SscTraceFV }

  procedure SscTracePV(var ssc: ssctype);
  begin
    with ssc do
      begin
        WritePrefix(tracefile, 'pv');
        WriteStr(tracefile, VariationPosEncode(predvar, rootpos));
        WriteStrNL(tracefile, '   score: ' + EncodeSv(predsv));
      end
  end; { SscTracePV }

  procedure SscTraceST(var ssc: ssctype);
  begin
    with ssc do
      begin
        WritePrefix(tracefile, 'st');
        WriteStrNL(tracefile, stnames[st])
      end
  end; { SscTraceST }

  procedure SscTraceTS(var ssc: ssctype);
  begin
    with ssc do
      begin
        WritePrefix(tracefile, 'ts');
        WriteStrNL(tracefile, EncodeCT(nodecount, usedusec))
      end
  end; { SscTraceTS }

  procedure SscTTReset(var ssc: ssctype);
  begin
    with ssc do
      begin
        if ttevalptr <> nil then
          TTEvalReset(ttevalptr^);
        if ttmainptr <> nil then
          TTMainReset(ttmainptr^);
        if ttpawnptr <> nil then
          TTPawnReset(ttpawnptr^);
        if tbwrangler.tttbasptr <> nil then
          TTTbasReset(tbwrangler.tttbasptr^)
      end
  end; { SscTTReset }

  procedure SscReadySet(var ssc: ssctype; var optnset: optnsettype; var pos: postype; mgm: mgmtype);
  begin
    with ssc do
      begin
        SscReset(ssc);
        TimerStart(ssctimer);
        sscoptnset := optnset;
        PosLoadFromPos(rootpos, pos);
        PosLoadFromPos(currpos, pos);
        case mgm of
          mgmnotated:     PosMetaGenNotated(rootpos, rootgms);
          mgmcanonical:   PosMetaGenCanonical(rootpos, rootgms);
          mgmdeluxe:      PosMetaGenDeluxe(rootpos, rootgms);
          mgmsuperdeluxe: PosMetaGenSuperDeluxe(rootpos, rootgms);
          mgmhyperdeluxe: PosMetaGenHyperDeluxe(rootpos, rootgms, tbwrangler);
        end { case }
      end
  end; { SscReadySet }

  procedure SscSelectQuick(var ssc: ssctype);
    var
      index: Integer;
      certaincount: Integer;
  begin
    with ssc do
      begin

      { Set up }

      certaincount := GmsCountCertain(rootgms);

      { Test: Checkmated/stalemated }

      if SScIsGoing(ssc) then
        if rootgms.movecount = 0 then
          begin
            if rootpos.inch then
              predsv := svcheckmated
            else
              predsv := sveven;
            SscStop(ssc, stnomoves)
          end;

      { Test: Quick checkmate }

      if SScIsGoing(ssc) then
        if certaincount > 0 then
          if IsSvMating(GmsBestCertainScore(rootgms)) then
            begin
              predsv := GmsBestCertainScore(rootgms);
              index := GmsIndexFirstMatchCertainScore(rootgms, predsv);
              VariationAppendMove(predvar, rootgms.moves[index]);
              SscStop(ssc, stquickmate)
            end;

      { Test: All certain, so either a quick lose or a quick draw }

      if SScIsGoing(ssc) then
        if certaincount = rootgms.movecount then
          begin
            predsv := GmsBestCertainScore(rootgms);
            index := GmsIndexFirstMatchCertainScore(rootgms, predsv);
            VariationAppendMove(predvar, rootgms.moves[index]);
            if IsSvLosing(predsv) then
              SscStop(ssc, stquicklose)
            else
              SscStop(ssc, stquickdraw)
          end;

      { Test: Singleton }

      if SScIsGoing(ssc) then
        if rootgms.movecount = 1 then
          begin
            predsv := sveven;
            index := 0;
            VariationAppendMove(predvar, rootgms.moves[index]);
            SscStop(ssc, stsingleton)
          end;

      { Test: All bad but one }

      if SScIsGoing(ssc) then
        if certaincount = (rootgms.movecount - 1) then
          if IsSvLosing(GmsBestCertainScore(rootgms)) then
            begin
              predsv := sveven;
              index := GmsIndexFirstUncertain(rootgms);
              VariationAppendMove(predvar, rootgms.moves[index]);
              SscStop(ssc, stallbadbutone)
            end

      end
  end; { SscSelectQuick }

  procedure SpookyFindMove(var ssc: ssctype); forward;

  procedure SscSelectSearch(var ssc: ssctype);
  begin
    SpookyFindMove(ssc)
  end; { SscSelectSearch }

  procedure SscSelect(var ssc: ssctype);
  begin
    with ssc do
      begin

        { Try a quick selection to avoid a general search }

        SscSelectQuick(ssc);

        { If no result from the quick selection attempt, then run the general search }

        if SScIsGoing(ssc) then
          SscSelectSearch(ssc);

        { Stop the timer and assign search elapsed time usage }

        TimerStop(ssctimer);
        usedusec := TimerCurrent(ssctimer);

        { Ensure that the PV is fully notated }

        VariationNotate(predvar, rootpos);

        { Trace: final (predicted) variation }

        if optntrfv in sscoptnset then
          SscTraceFV(ssc);

        { Trace: search termination }

        if optntrst in sscoptnset then
          SscTraceST(ssc);

        { Trace: EPD analysis output }

        if optntrea in sscoptnset then
          SscTraceEA(ssc);

        { Trace: timing statistics }

        if optntrts in sscoptnset then
          SscTraceTS(ssc)

      end
  end; { SscSelect }

  { ***** Smokey mate finder routines ***** }

  procedure SmokeyFindMate(var ssc: ssctype; fmvc: Integer);
    var
      ply: plytype;

    procedure SmokeySearch;
      var
        moveindex: Integer;

      procedure SmokeyApplyKillerBonus;
        var
          index: Integer;
      begin
        with ssc, pirvec[ply] do
          begin
            index := GmsLocateMove(gms, killers.k0move);
            if index >= 0 then
              Inc(gms.moves[index].sv, 16);
            index := GmsLocateMove(gms, killers.k1move);
            if index >= 0 then
              Inc(gms.moves[index].sv, 8)
          end
      end; { SmokeyApplyKillerBonus }

    begin
      with ssc do
        while pirvec[ply].nss <> nssexit do
          case pirvec[ply].nss of

            nssplystart:
              with pirvec[ply] do
                begin
                  Inc(nodecount);
                  PirClear(pirvec[ply]);
                  if optntrcv in sscoptnset then
                    SscTraceCV(ssc);
                  nss := nsstermtest
                end;

            nsstermtest:
              with pirvec[ply] do
                if depth = 0 then
                  begin
                    if PosIsCheckmate(currpos) then
                      window.alfa := svcheckmated
                    else
                      window.alfa := sveven;
                    nss := nssplyfinish
                  end
                else
                  nss := nssgenerate;

            nssgenerate:
              with pirvec[ply] do
                begin
                  if depth = 1 then
                    PosGenOnlyChecks(currpos, gms)
                  else
                    begin
                      PosGenerate(currpos, gms);
                      PosApplyOrderAntiMobility(currpos, gms);
                      SmokeyApplyKillerBonus
                    end;
                  if gms.movecount = 0 then
                    begin
                      if currpos.inch then
                        window.alfa := svcheckmated
                      else
                        window.alfa := sveven;
                      nss := nssplyfinish
                    end
                  else
                    nss := nssmovepick
                end;

            nssmovepick:
              with pirvec[ply] do
                if (pickcount = gms.movecount) or WindowIsClosed(window) or
                    (ispzmover and IsSvMating(window.alfa)) or
                    (not ispzmover and not IsSvLosing(window.alfa)) then
                  nss := nsspostscan
                else
                  begin
                    moveindex := GmsBestUnsearchedIndex(gms);
                    MoveFlagSet(gms.moves[moveindex], mfsrch);
                    srchmove := gms.moves[moveindex];
                    Inc(pickcount);
                    nss := nssexecute
                  end;

            nssexecute:
              begin
                with pirvec[ply] do
                  begin
                    VariationAppendMove(currvar, srchmove);
                    WindowShiftDn(window, pirvec[ply + 1].window);
                    pirvec[ply + 1].depth := depth - 1;
                    PosExecute(currpos, srchmove)
                  end;
                Inc(ply);
                pirvec[ply].nss := nssplystart
              end;

            nssretract:
              begin
                Dec(ply);
                with pirvec[ply] do
                  begin
                    PosRetract(currpos);
                    srchsv := CalcSvUp(pirvec[ply + 1].window.alfa);
                    VariationRecycleTail(currvar);
                    if srchsv > window.alfa then
                      begin
                        bestmove := srchmove;
                        window.alfa := srchsv;
                        if srchsv < window.beta then
                          VariationBuild(pv, bestmove, pirvec[ply + 1].pv)
                      end;
                    nss := nssmovepick
                  end
              end;

            nsspostscan:
              with pirvec[ply] do
                begin
                  if not MoveFlagTest(bestmove, mfvoid) then
                    KillersAddMove(killers, bestmove);
                  nss := nssplyfinish
                end;

            nssplyfinish:
              with pirvec[ply] do
                if ply > 0 then
                  nss := nssretract
                else
                  nss := nssexit;

          end { case }
    end; { SmokeySearch }

  begin
    with ssc do
      begin

        { The root is always at ply zero }

        ply := 0;

        { Run the mate finder }

        with pirvec[ply] do
          begin
            nss := nssplystart;
            window := rootwindow;
            depth := (fmvc * 2) - 1;
            SmokeySearch;
            predsv := window.alfa;
            VariationAssign(predvar, pv)
          end;

        { Stop the timer and assign search elapsed time usage }

        TimerStop(ssctimer);
        usedusec := TimerCurrent(ssctimer);

        { Handle the predicted variation and the search termination }

        if IsSvMating(predsv) then
          begin
            VariationNotate(predvar, rootpos);
            SscStop(ssc, stforcedmate)
          end
        else
          begin
            VariationRecycle(predvar);
            SscStop(ssc, stlimitdepth)
          end

      end
  end; { SmokeyFindMate }

  { ***** Lucky evaluation routines ***** }

  function LuckyEvaluatePawnsNoTrans(var ssc: ssctype; var pawnstruct: pawnstructtype): svtype;
    var
      myresult: svtype;
      color: colorrtype;
      csvs: array [colorrtype] of svtype;
      count: cctype;
      bb: bbtype;
      sq: sqxtype;
  begin
    with ssc, currpos, pawnstruct do
      begin

        { Build the pawn structure components from the current position }

        PawnStructLoadFromPos(pawnstruct, currpos);

        { Cycle once per each color }

        for color := colorrmin to colorrmax do
          begin

            { Reset the accumulator for the current color }

            csvs[color] := 0;

            { Pawn structure component: backward }

            count := BbCount(backward[color]);
            Inc(csvs[color], (count * escsvvec[escpawnbackward]));

            { Pawn structure component: connected }

            count := BbCount(connected[color]);
            Inc(csvs[color], (count * escsvvec[escpawnconnected]));

            { Pawn structure component: isolated }

            count := BbCount(isolated[color]);
            Inc(csvs[color], (count * escsvvec[escpawnisolated]));

            { Pawn structure component: location }

            bb := location[color];
            repeat
              sq := BbNextSq(bb);
              if sq <> sqnil then
                Inc(csvs[color], (pawnloc0[color, sq] * escsvvec[escpawnlocation]))
            until sq = sqnil;

            { Pawn structure component: majority }

            count := BbCount(majority[color]);
            Inc(csvs[color], (count * escsvvec[escpawnmajority]));

            { Pawn structure component: multiple }

            count := BbCount(multiple[color]);
            Inc(csvs[color], (count * escsvvec[escpawnmultiple]));

            { Pawn structure component: passed }

            bb := passed[color];
            repeat
              sq := BbNextSq(bb);
              if sq <> sqnil then
                Inc(csvs[color], (pawnloc1[color, sq] * escsvvec[escpawnpassed]))
            until sq = sqnil

          end;

        { Assign result based on active color }

        myresult := csvs[good] - csvs[evil]
      end;
    LuckyEvaluatePawnsNoTrans := myresult
  end; { LuckyEvaluatePawnsNoTrans }

  function LuckyEvaluatePawns(var ssc: ssctype; var pawnstruct: pawnstructtype): svtype;
    var
      myresult: svtype;
  begin
    with ssc do

      { Test: Pawn transposititon table availability }

      if ttpawnptr <> nil then
        begin

          { Try an element fetch and test if not present }

          TTPawnFetchEntry(ttpawnptr^, currpos, myresult, pawnstruct);
          if IsSvBroken(myresult) then
            begin

              { Unsuccessful fetch; calculate result then stash }

              myresult := LuckyEvaluatePawnsNoTrans(ssc, pawnstruct);
              TTPawnStashEntry(ttpawnptr^, currpos, myresult, pawnstruct)
            end
        end
      else
        myresult := LuckyEvaluatePawnsNoTrans(ssc, pawnstruct);
    LuckyEvaluatePawns := myresult
  end; { LuckyEvaluatePawns }

  function LuckyEvaluateKnights(var ssc: ssctype; var pawnstruct: pawnstructtype): svtype;
    var
      color: colorrtype;
      csvs: array [colorrtype] of svtype;
      bb: bbtype;
      sq: sqxtype;
  begin
    with ssc, currpos, bbdb do
      begin
        for color := colorrmin to colorrmax do
          begin

            { Reset the accumulator }

            csvs[color] := 0;

            { Mobility: Knights }

            bb := locbm[synthknight[color]];
            repeat
              sq := BbNextSq(bb);
              if sq <> sqnil then
                if not BbTestSq(pmbb, sq) then
                  Inc(csvs[color], knightatkccvec[sq] * escsvvec[escmobilityknight])
            until sq = sqnil

          end;
        LuckyEvaluateKnights := csvs[good] - csvs[evil]
      end
  end; { LuckyEvaluateKnights }

  function LuckyEvaluateBishops(var ssc: ssctype; var pawnstruct: pawnstructtype): svtype;
    var
      color: colorrtype;
      csvs: array [colorrtype] of svtype;
      bb: bbtype;
      sq: sqxtype;
  begin
    with ssc, currpos, bbdb do
      begin
        for color := colorrmin to colorrmax do
          begin

            { Reset the accumulator }

            csvs[color] := 0;

            { Mobility: Bishops }

            bb := locbm[synthbishop[color]];
            repeat
              sq := BbNextSq(bb);
              if sq <> sqnil then
                if not BbTestSq(pmbb, sq) then
                  Inc(csvs[color], BbCount(atkfs[sq]) * escsvvec[escmobilitybishop])
            until sq = sqnil

          end;
        LuckyEvaluateBishops := csvs[good] - csvs[evil]
      end
  end; { LuckyEvaluateBishops }

  function LuckyEvaluateRooks(var ssc: ssctype; var pawnstruct: pawnstructtype): svtype;
    var
      color: colorrtype;
      csvs: array [colorrtype] of svtype;
      bb: bbtype;
      sq: sqxtype;
  begin
    with ssc, currpos, bbdb do
      begin
        for color := colorrmin to colorrmax do
          begin

            { Reset the accumulator }

            csvs[color] := 0;

            { Mobility: Rooks }

            bb := locbm[synthrook[color]];
            repeat
              sq := BbNextSq(bb);
              if sq <> sqnil then
                if not BbTestSq(pmbb, sq) then
                  Inc(csvs[color], BbCount(atkfs[sq]) * escsvvec[escmobilityrook])
            until sq = sqnil

          end;
        LuckyEvaluateRooks := csvs[good] - csvs[evil]
      end
  end; { LuckyEvaluateRooks }

  function LuckyEvaluateQueens(var ssc: ssctype; var pawnstruct: pawnstructtype): svtype;
    var
      color: colorrtype;
      csvs: array [colorrtype] of svtype;
      bb: bbtype;
      sq: sqxtype;
  begin
    with ssc, currpos, bbdb do
      begin
        for color := colorrmin to colorrmax do
          begin

            { Reset the accumulator }

            csvs[color] := 0;

            { Mobility: Queens }

            bb := locbm[synthqueen[color]];
            repeat
              sq := BbNextSq(bb);
              if sq <> sqnil then
                if not BbTestSq(pmbb, sq) then
                  Inc(csvs[color], BbCount(atkfs[sq]) * escsvvec[escmobilityqueen])
            until sq = sqnil

          end;
        LuckyEvaluateQueens := csvs[good] - csvs[evil]
      end
  end; { LuckyEvaluateQueens }

  function LuckyEvaluateKings(var ssc: ssctype; var pawnstruct: pawnstructtype): svtype;
    var
      myresult: svtype;
  begin
    myresult := sveven; {TBD}
    LuckyEvaluateKings := myresult
  end; { LuckyEvaluateKings }

  function LuckyEvaluateNoTrans(var ssc: ssctype): svtype;
    var
      myresult: svtype;
      pawnstruct: pawnstructtype;
  begin
    with ssc, currpos do
      begin

        { Initialize the result from the raw material totals }

        myresult := matv[good] - matv[evil];

        { Side to move bonus }

        Inc(myresult, escsvvec[escsidetomove]);

        { Fold in the pawns evaluation; this also defines the pawn structure object }

        Inc(myresult, LuckyEvaluatePawns(ssc, pawnstruct));

        { Fold in the knights evaluation }

        Inc(myresult, LuckyEvaluateKnights(ssc, pawnstruct));

        { Fold in the bishops evaluation }

        Inc(myresult, LuckyEvaluateBishops(ssc, pawnstruct));

        { Fold in the rooks evaluation }

        Inc(myresult, LuckyEvaluateRooks(ssc, pawnstruct));

        { Fold in the queens evaluation }

        Inc(myresult, LuckyEvaluateQueens(ssc, pawnstruct));

        { Fold in the kings evaluation }

        Inc(myresult, LuckyEvaluateKings(ssc, pawnstruct))

      end;
    LuckyEvaluateNoTrans := myresult
  end; { LuckyEvaluateNoTrans }

  function LuckyEvaluate(var ssc: ssctype): svtype;
    var
      myresult: svtype;
  begin
    with ssc do

      { Test: Evaluation transposititon table availability }

      if ttevalptr <> nil then
        begin

          { Try an element fetch and test if not present }

          TTEvalFetchScore(ttevalptr^, currpos, myresult);
          if IsSvBroken(myresult) then
            begin

              { Unsuccessful fetch; calculate result then stash }

              myresult := LuckyEvaluateNoTrans(ssc);
              TTEvalStashScore(ttevalptr^, currpos, myresult)
            end
        end
      else
        myresult := LuckyEvaluateNoTrans(ssc);
    LuckyEvaluate := myresult
  end; { LuckyEvaluate }

  { ***** Spooky search routines ***** }

  procedure SpookyFindMove(var ssc: ssctype);
    var
      ply: plytype;

    procedure SpookyPrepareRoot;
      var
        index: Integer;
    begin
      with ssc, rootgms do
        begin
          PosLoadFromPos(currpos, rootpos);
          for index := 0 to movecount - 1 do
            if not MoveFlagTest(moves[index], mfcert) then
              begin
                PosExecute(currpos, moves[index]);
                moves[index].sv := CalcSvUp(LuckyEvaluate(ssc));
                PosRetract(currpos)
              end;
          GmsSortByScore(rootgms)
        end
    end; { SpookyPrepareRoot }

    procedure SpookyIterationSequence;
      var
        iter: Integer;

      procedure SpookyIterate;

        procedure SpookySearch;

          procedure SpookyLimitTestNode;
          begin
            if iter > 0 then
              with ssc, srl do
                case srlf of
                  srlfnode:
                    if nodecount >= limitnode then
                      SscStop(ssc, stlimitnode);
                  srlfftim:
                    if (nodecount mod 1024) = 0 then
                      if TimerCurrent(ssctimer) >= limitftim then
                        SscStop(ssc, stlimittime);
                end { case }
          end; { SpookyLimitTestNode }

          procedure SpookyMovePick;
            var
              found: Boolean;
              moveindex: Integer;
              testmove: movetype;

            procedure SpookyOrderMoves;
              var
                killerindex: Integer;
            begin
              with ssc, pirvec[ply] do
                begin
                  PosApplyOrderEstimatedGain(currpos, gms);
                  killerindex := GmsLocateMove(gms, killers.k0move);
                  if killerindex >= 0 then
                    Inc(gms.moves[killerindex].sv, svpvpawn);
                  killerindex := GmsLocateMove(gms, killers.k1move);
                  if killerindex >= 0 then
                    Inc(gms.moves[killerindex].sv, (svpvpawn div 2))
                end
            end; { SpookyOrderMoves }

            procedure SpookyPickThis(index: Integer);
            begin
              with ssc, pirvec[ply] do
                begin
                  MoveFlagSet(gms.moves[index], mfsrch);
                  srchmove := gms.moves[index];
                  Inc(pickcount);
                  found := True
                end
            end; { SpookyPickThis }

          begin
            found := False;
            with ssc, pirvec[ply] do
              while not found do
                case pms of

                  { Pick move state: Start move pick operations for this node }

                  pmsstart:
                    if isplyzero then
                      pms := pmscyclenext
                    else
                      pms := pmspredvar;

                  { Pick move state: Cycle through moves in generation order }

                  pmscyclenext:
                    SpookyPickThis(GmsFirstUnsearchedIndex(gms));

                  { Pick move state: Cycle through moves in score order  }

                  pmscyclebest:
                    SpookyPickThis(GmsBestUnsearchedIndex(gms));

                  { Pick move state: Apply move ordering }

                  pmsordering:
                    begin
                      SpookyOrderMoves;
                      pms := pmscyclebest
                    end;

                  { Pick move state: Attempt to follow the prior predicted variaiton }

                  pmspredvar:
                    begin
                      if isleftmost and (ply < VariationLength(priorpv)) then
                        begin
                          VariationFetchNthMove(priorpv, ply, testmove);
                          SpookyPickThis(GmsLocateMoveNoFail(gms, testmove))
                        end;
                      pms := pmstranstable
                    end;

                  { Pick move state: Attempt a transposition table hint }

                  pmstranstable:
                    begin
                      if ttmainptr <> nil then
                        begin
                          TTMainFetchHintMove(ttmainptr^, currpos, testmove);
                          if not MoveFlagTest(testmove, mfvoid) then
                            begin
                              moveindex := GmsLocateMove(gms, testmove);
                              if moveindex >= 0 then
                                if not MoveFlagTest(gms.moves[moveindex], mfsrch) then
                                  SpookyPickThis(moveindex)
                            end
                        end;
                      pms := pmsordering
                    end;

                end { case }
          end; { SpookyMovePick }

          procedure SpookyMinimax;
          begin
            with ssc, pirvec[ply] do
              begin

                { Test: best score so far at this node }

                if srchsv > window.alfa then
                  begin

                    { Assign the best move so far and update alpha }

                    bestmove := srchmove;
                    window.alfa := srchsv;

                    { Test: best score inside window }

                    if srchsv < window.beta then
                      begin

                        { Update the predicted variation for this node }

                        VariationBuild(pv, bestmove, pirvec[ply + 1].pv);

                        { Ply zero PV update gets extra treatment }

                        if isplyzero then
                          begin

                            { Ensure notated variation data }

                            VariationNotate(pv, rootpos);

                            { Assign top level search result PV and score }

                            VariationAssign(predvar, pv);
                            predsv := window.alfa;

                            { Update the iteration indexed predicted score }

                            iirvec[iter].sv := predsv;

                            { Trace: predicted variation }

                            if optntrpv in sscoptnset then
                              SscTracePV(ssc)
                          end
                      end;

                    { If at the root, then rotate the best move to the front of the pick list }

                    if isplyzero then
                      GmsMoveToFront(rootgms, bestmove)
                  end
              end
          end; { SpookyMinimax }

        begin
          with ssc do
            while pirvec[ply].nss <> nssexit do
              case pirvec[ply].nss of

                { Search state: Initialize processing at this node }

                nssplystart:
                  with pirvec[ply] do
                    begin
                      Inc(nodecount);
                      PirClear(pirvec[ply]);
                      if optntrcv in sscoptnset then
                        SscTraceCV(ssc);
                      if isleftmost and (optntrfd in sscoptnset) then
                        SscTraceFD(ssc);
                      SpookyLimitTestNode;
                      if SScIsStopped(ssc) then
                        begin
                          window.alfa := svbroken;
                          nss := nssplyfinish
                        end
                      else
                        if isplyone and MoveFlagTest(pirvec[0].srchmove, mfcert) then
                          begin
                            window.alfa := CalcSvDn(pirvec[0].srchmove.sv);
                            nss := nssplyfinish
                          end
                        else
                          if islastply then
                            begin
                              window.alfa := LuckyEvaluate(ssc);
                              nss := nssplyfinish
                            end
                          else
                            begin
                              if (depth <= 0) and not currpos.inch then
                                isgainersonly := True;
                              if currpos.inch then
                                Inc(extension);
                              nss := nssfirdrawtest
                            end
                    end;

                { Search state: Draw tests for fiftymoves/insufficient/repetition }

                nssfirdrawtest:
                  with pirvec[ply] do
                    if isdrawtest and PosIsDrawFIR(currpos) then
                      begin
                        window.alfa := sveven;
                        nss := nssplyfinish
                      end
                    else
                      if isgainersonly then
                        nss := nssstandtest
                      else
                        nss := nsstbprobe;

                { Search state: Probe the tablebases }

                nsstbprobe:
                  with pirvec[ply] do
                    if not isplyzero and (currpos.wood <= tbmmax) and
                        ((currpos.census.mic[manwp] = 0) or (currpos.census.mic[manbp] = 0)) then
                      begin
                        srchsv := TbWranglerProbe(tbwrangler, currpos);
                        if not IsSvBroken(srchsv) then
                          begin
                            window.alfa := srchsv;
                            nss := nssplyfinish
                          end
                        else
                          nss := nssgenerate
                      end
                    else
                      nss := nssgenerate;

                { Search state: Gainer search stand-pat evaluation and test }

                nssstandtest:
                  with pirvec[ply] do
                    begin
                      standsv := LuckyEvaluate(ssc);
                      if standsv > window.alfa then
                        begin
                          window.alfa := standsv;
                          if standsv >= window.beta then
                            nss := nssplyfinish
                        end
                      else
                        nss := nssgenerate
                    end;

                { Search state: Move generation }

                nssgenerate:
                  with pirvec[ply] do
                    if isplyzero then
                      begin
                        GmsLoadFromGms(gms, rootgms);
                        nss := nssmovepick
                      end
                    else
                      if isgainersonly then
                        begin
                          PosGenOnlyGainers(currpos, gms);
                          nss := nssmovepick
                        end
                      else
                        begin
                          PosGenerate(currpos, gms);
                          if gms.movecount = 0 then
                            begin
                              if currpos.inch then
                                window.alfa := svcheckmated
                              else
                                window.alfa := sveven;
                              nss := nssplyfinish
                            end
                          else
                            nss := nssmovepick
                        end;

                { Search state: Move pick }

                nssmovepick:
                  with pirvec[ply] do
                    if SscIsStopped(ssc) or (pickcount = gms.movecount) or WindowIsClosed(window) then
                      nss := nsspostscan
                    else
                      begin
                        SpookyMovePick;
                        if isgainersonly then
                          begin
                            if (standsv + MoveBestGain(srchmove)) > window.alfa then
                              nss := nssexecute
                          end
                        else
                          nss := nssexecute
                      end;

                { Search state: Execute the move and advance one ply }

                nssexecute:
                  begin
                    with pirvec[ply] do
                      begin
                        WindowShiftDn(window, pirvec[ply + 1].window);
                        pirvec[ply + 1].depth := depth - 1 + extension;
                        VariationAppendMove(currvar, srchmove);
                        PosExecute(currpos, srchmove);
                      end;
                    Inc(ply);
                    pirvec[ply].nss := nssplystart
                  end;

                { Search state: Retreat one ply and retract the move }

                nssretract:
                  begin
                    Dec(ply);
                    with pirvec[ply] do
                      begin
                        PosRetract(currpos);
                        VariationRecycleTail(currvar);
                        if SScIsStopped(ssc) then
                          begin
                            window.alfa := svbroken;
                            nss := nssplyfinish
                          end
                        else
                          begin
                            srchsv := CalcSvUp(pirvec[ply + 1].window.alfa);
                            SpookyMinimax;
                            nss := nssmovepick
                          end
                      end
                  end;

                { Search state: Post move scan operations }

                nsspostscan:
                  with pirvec[ply] do
                    begin
                      if not MoveFlagTest(bestmove, mfvoid) then
                        begin
                          if ttmainptr <> nil then
                            TTMainStashHintMove(ttmainptr^, currpos, bestmove);
                          if not MoveIsGainer(bestmove) then
                            KillersAddMove(killers, bestmove)
                        end;
                      nss := nssplyfinish
                    end;

                { Search state: Final processing for this node }

                nssplyfinish:
                  with pirvec[ply] do
                    begin
                      isleftmost := False;
                      if isplyzero then
                        nss := nssexit
                      else
                        nss := nssretract
                    end;

              end { case }
        end; { SpookySearch }

      begin
        with ssc do
          begin

            { Trace: iteration start }

            if optntrit in sscoptnset then
              begin
                WritePrefix(tracefile, 'it');
                WriteStrNL(tracefile, EncodeInteger(iter) + ' start')
              end;

            { Run the search for this iteration }

            isleftmost := True;
            with pirvec[ply] do
              begin
                nss := nssplystart;
                window := rootwindow;
                depth := iter + 1;
                SpookySearch;
                if SScIsGoing(ssc) then
                  VariationAssign(priorpv, pv)
              end;

            { Trace: iteration finish }

            if optntrit in sscoptnset then
              begin
                WritePrefix(tracefile, 'it');
                WriteStrNL(tracefile, EncodeInteger(iter) + ' finish')
              end

          end
      end; { SpookyIterate }

    begin
      with ssc do
        begin

          { Initialize the iteration index }

          iter := itermin;

          { Loop with one iteration per cycle }

          while SscIsGoing(ssc) and (iter <= itermax) do
            begin

              { Run one iteration }

              SpookyIterate;

              { Handle early mate detection }

              if SscIsGoing(ssc) and (iter > 1) then
                if IsSvMating(iirvec[iter].sv) and IsSvMating(iirvec[iter - 1].sv) then
                  SscStop(ssc, stforcedmate);

              { Handle early lose detection }

              if SscIsGoing(ssc) and (iter > 1) then
                if IsSvLosing(iirvec[iter].sv) and IsSvLosing(iirvec[iter - 1].sv) then
                  SscStop(ssc, stforcedlose);

              { Next iteration }

              Inc(iter)

            end;

          { Ensure search termination }

          if SscIsGoing(ssc) then
            SscStop(ssc, stlimitdepth)

        end
    end; { SpookyIterationSequence }

  begin
    with ssc do
      begin

        { The root is always at ply zero }

        ply := 0;

        { Generate initial move ordering at the root }

        SpookyPrepareRoot;

        { Run the iteration sequence starting with iteration = 0 and depth = 1 }

        SpookyIterationSequence;

      end
  end; { SpookyFindMove }

  { ***** Command processing context routines ***** }

  procedure CpcNewGame(var cpc: cpctype);
  begin
    with cpc do
      begin
        PosLoadInitialArray(cpcpos);
        PgnGameLoadFromPos(pgngame, cpcpos);
        SscTTReset(sscptrvec[0]^) {TBD}
      end
  end; { CpcNewGame }

  procedure CpcInit(var cpc: cpctype);
    var
      core: coretype;
      corecount: Integer;
  begin
    with cpc do
      begin

        { Basic initialization }

        TimerResetThenStart(cpctimer);
        cpcoptnset := [];
        PrngRandomize(prng);
        ifile := Input;
        ofile := Output;
        efile := StdErr;
        exiting := False;
        TokenListInit(ctlist);
        PosInit(cpcpos);
        PgnGameInit(pgngame);

        { Initialize selection/search contexts }

        corecount := CalcCoreCount;
        for core := coremin to corecount - 1 do
          begin
            New(sscptrvec[core]);
            SscInit(sscptrvec[core]^);
            sscptrvec[core]^.tracefile := ofile
          end;
        for core := corecount to coremax do
          sscptrvec[core] := nil;

        { Set for a new game }

        CpcNewGame(cpc)

      end
  end; { CpcInit }

  procedure CpcTerm(var cpc: cpctype);
    var
      core: coretype;
  begin
    with cpc do
      begin

        { Basic termination }

        TokenListTerm(ctlist);
        PosTerm(cpcpos);
        PgnGameTerm(pgngame);

        { Terminate selection/search contexts }

        for core := coremin to coremax do
          if sscptrvec[core] <> nil then
          begin
            SscTerm(sscptrvec[core]^);
            Dispose(sscptrvec[core]);
          end;

      end
  end; { CpcTerm }

  procedure CpcPlayMove(var cpc: cpctype; var move: movetype);
  begin
    with cpc do
      begin
        PosMoveNotate(cpcpos, move);
        PosExecute(cpcpos, move);
        PgnGameAddMove(pgngame, move);
        PgnGameSetResult(pgngame, PosCalcGr(cpcpos))
      end
  end; { CpcPlayMove }

  procedure CpcUnplayMove(var cpc: cpctype);
  begin
    with cpc do
      begin
        PosRetract(cpcpos);
        PgnGameDelMove(pgngame);
        PgnGameSetResult(pgngame, PosCalcGr(cpcpos))
      end
  end; { CpcUnplayMove }

  procedure CpcSnycPgnGame(var cpc: cpctype);
  begin
    with cpc do
      PgnGameLoadFromPos(pgngame, cpcpos)
  end; { CpcSnycPgnGame }

  { ***** Interactive command processor routines ***** }

  procedure IcpUserError(var icp: icptype; str: String);
  begin
    with icp, cpc do
      WriteStrNL(efile, 'Error: ' + str)
  end; { IcpUserError }

  procedure IcpUserErrorNoParms(var icp: icptype);
  begin
    IcpUserError(icp, 'Need exactly zero parameters')
  end; { IcpUserErrorNoParms }

  procedure IcpUserErrorOneParm(var icp: icptype);
  begin
    IcpUserError(icp, 'Need exactly one parameter')
  end; { IcpUserErrorOneParm }

  procedure IcpUserErrorTwoParms(var icp: icptype);
  begin
    IcpUserError(icp, 'Need exactly two parameters')
  end; { IcpUserErrorTwoParms }

  procedure IcpUserErrorNeedAtLeastOneParm(var icp: icptype);
  begin
    IcpUserError(icp, 'Need at least one parameter')
  end; { IcpUserErrorNeedAtLeastOneParm }

  procedure IcpDisplayBoardColor(var icp: icptype);
  begin
    with icp, cpc do
      WriteStr(ofile, BoardEncodeGraphicColor(cpcpos.board))
  end; { IcpDisplayBoardColor }

  procedure IcpDisplayBoardMono(var icp: icptype);
  begin
    with icp, cpc do
      WriteStr(ofile, BoardEncodeGraphicMono(cpcpos.board))
  end; { IcpDisplayBoardColor }

  procedure IcpDisplayElapsedTime(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(ofile, 'Elapsed time: ' + TimerEncode(cpctimer))
  end; { IcpDisplayElapsedTime }

  procedure IcpDisplayFen(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(ofile, 'FEN: ' + PosEncode(cpcpos))
  end; { IcpDisplayFen }

  procedure IcpDisplayHashes(var icp: icptype);
    var
      gamehash: hashtype;
  begin
    with icp, cpc do
      begin
        PosCalcGameHash(cpcpos, gamehash);
        WriteStrNL(
            ofile,
            'Hashes:' +
            ' Main: ' + HashEncode(cpcpos.mphc) +
            '   Pawn: ' + HashEncode(cpcpos.pshc) +
            '   Game: ' + HashEncode(gamehash))
      end
  end; { IcpDisplayHashes }

  procedure IcpDisplayID(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(ofile, progvers)
  end; { IcpDisplayID }

  procedure IcpDisplayMaterial(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(
        ofile,
        'Material:' +
        ' ' + playernames[colorw] + ': ' + EncodeSv(cpcpos.matv[colorw]) +
        '   ' + playernames[colorb] + ': ' + EncodeSv(cpcpos.matv[colorb]) +
        '   Total: ' + EncodeSv(cpcpos.matv[colorw] + cpcpos.matv[colorb]))
  end; { IcpDisplayMaterial }

  procedure IcpDisplayMaterialSignature(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(ofile, 'Material signature: ' + MsigName(cpcpos.msig))
  end; { IcpDisplayMaterialSignature }

  procedure IcpDisplayMoveCount(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(ofile, 'Move count: ' + EncodeInteger(PosCountMoves(cpcpos)))
  end; { IcpDisplayMoveCount }

  procedure IcpDisplayMoveList(var icp: icptype);
    var
      gms: gmstype;
  begin
    with icp, cpc do
      begin
        PosMetaGenCanonical(cpcpos, gms);
        WriteStrNL(ofile, 'Moves: ' + GmsEncode(gms))
      end
  end; { IcpDisplayMoveList }

  procedure IcpDisplayOptions(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(ofile, 'Options: ' + OptnSetEncode(cpcoptnset))
  end; { IcpDisplayOptions }

  procedure IcpDisplayPgn(var icp: icptype);
  begin
    with icp, cpc do
      WriteStr(ofile, PgnGameEncode(pgngame))
  end; { IcpDisplayPgn }

  procedure IcpDisplayPlyCount(var icp: icptype);
  begin
    with icp, cpc do
      WriteStrNL(ofile, 'Played moves count: ' + EncodeInteger(cpcpos.usedspevlist.ecount))
  end; { IcpDisplayPlyCount }

  procedure IcpDisplayPosition(var icp: icptype);
  begin
    with icp, cpc do
      begin
        if optnmono in cpcoptnset then
          IcpDisplayBoardMono(icp)
        else
          IcpDisplayBoardColor(icp);
        WriteStrNL(ofile, 'FEN: ' + PosEncode(cpcpos))
      end
  end; { IcpDisplayPosition }

  procedure IcpPlayMove(var icp: icptype; var move: movetype);
    var
      mc: mctype;
      gt: gttype;
  begin
    with icp, cpc do
      begin
        PosLoadToMc(cpcpos, mc);
        WriteStrNL(ofile, 'Playing: ' + MoveEncodeMc(move, mc));
        CpcPlayMove(cpc, move);
        if optnadcp in cpcoptnset then
          IcpDisplayPosition(icp);
        gt := PosCalcGt(cpcpos);
        if gt <> gtunterminated then
          WriteStrNL(ofile, 'Game over: ' + gtnames[gt])
      end
  end; { IcpPlayMove }

  procedure IcpUnplayMove(var icp: icptype);
    var
      mc: mctype;
      move: movetype;
  begin
    with icp, cpc do
      begin
        PosLoadToMc(cpcpos, mc);
        McDecrement(mc);
        move := cpcpos.usedspevlist.tail^.spevmove;
        WriteStrNL(ofile, 'Unplaying: ' + MoveEncodeMc(move, mc));
        CpcUnplayMove(cpc);
        if optnadcp in cpcoptnset then
          IcpDisplayPosition(icp)
      end
  end; { IcpUnplayMove }

  procedure IcpPerft(var icp: icptype; perft: perfttype);
    var
      tokenptr: tokenptrtype;
      depth: Integer;
      pathcount: nctype;
      tasktimer: timertype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        begin
          tokenptr := ctlist.head^.next;
          if not IsStringUnsignedInteger(tokenptr^.tstr) then
            IcpUserError(icp, 'Parameter must be an unsigned integer')
          else
            begin
              depth := DecodeUnsignedInteger(tokenptr^.tstr);
              if optntrif in cpcoptnset then
                begin
                  WritePrefix(ofile, 'if');
                  WriteStrNL(ofile, PosEncode(cpcpos))
                end;
              TimerResetThenStart(tasktimer);
              case perft of
                perftbulk: pathcount := PosPerftBulk(cpcpos, ofile, depth, True);
                perftfull: pathcount := PosPerftFull(cpcpos, ofile, depth, True);
                perfttran: pathcount := PosPerftTran(cpcpos, ofile, depth, True)
              end; { case }
              TimerStop(tasktimer);
              if optntrts in cpcoptnset then
                begin
                  WritePrefix(ofile, 'ts');
                  WriteStrNL(ofile, EncodeCT(pathcount, TimerCurrent(tasktimer)))
                end
            end
        end
  end; { IcpPerft }

  procedure IcpDoCbench(var icp: icptype);
    var
      nodecount: nctype;
      tasktimer: timertype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        begin
          WriteStrNL(ofile, 'Running benchmark');
          TimerResetThenStart(tasktimer);
          nodecount := Bench;
          TimerStop(tasktimer);
          WriteStrNL(ofile, EncodeCT(nodecount, TimerCurrent(tasktimer)))
        end
  end; { IcpDoCbench }

  procedure IcpDoCd(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        begin
          IcpDisplayID(icp);
          IcpDisplayOptions(icp);
          IcpDisplayPosition(icp);
          IcpDisplayPlyCount(icp);
          IcpDisplayMoveCount(icp);
          IcpDisplayMoveList(icp);
          IcpDisplayMaterial(icp);
          IcpDisplayMaterialSignature(icp);
          IcpDisplayHashes(icp);
          IcpDisplayElapsedTime(icp);
          WriteNL(ofile);
          IcpDisplayPgn(icp)
        end
  end; { IcpDoCd }

  procedure IcpDoCdao(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayOptions(icp)
  end; { IcpDoCdao }

  procedure IcpDoCdb(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        if optnmono in cpcoptnset then
          IcpDisplayBoardMono(icp)
        else
          IcpDisplayBoardColor(icp)
  end; { IcpDoCdb }

  procedure IcpDoCdbbdb(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        BbdbWriteSqs(cpcpos.bbdb, ofile)
  end; { IcpDoCdbbdb }

  procedure IcpDoCdbcolor(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayBoardColor(icp)
  end; { IcpDoCdbcolor }

  procedure IcpDoCdbmono(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayBoardMono(icp)
  end; { IcpDoCdbmono }

  procedure IcpDoCdesc(var icp: icptype);
    var
      esc: esctype;
      str: String;
      index: Integer;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        for esc := escmin to escmax do
          begin
            str := escnames[esc];
            index := Length(str);
            while index < 16 do
              begin
                str := str + ' ';
                Inc(index)
              end;
            str := str + EncodeSv(escsvvec[esc]);
            WriteStrNL(ofile, str)
          end
  end; { IcpDoCdesc }

  procedure IcpDoCdfen(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayFen(icp)
  end; { IcpDoCdfen }

  procedure IcpDoCdm(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayMoveList(icp)
  end; { IcpDoCdm }

  procedure IcpDoCdmsig(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayMaterialSignature(icp)
  end; { IcpDoCdmsig }

  procedure IcpDoCdobm(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCdobm }

  procedure IcpDoCdp(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayPosition(icp)
  end; { IcpDoCdp }

  procedure IcpDoCdpgn(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayPgn(icp)
  end; { IcpDoCdpgn }

  procedure IcpDoCdpi(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpDisplayID(icp)
  end; { IcpDoCdpi }

  procedure IcpDoCdps(var icp: icptype);
    var
      pawnstruct: pawnstructtype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        begin
          PawnStructLoadFromPos(pawnstruct, cpcpos);
          WriteStr(ofile, PawnStructEncode(pawnstruct))
        end
  end; { IcpDoCdps }

  procedure IcpDoCdtbm(var icp: icptype);
    var
      gms: gmstype;
      index: Integer;
      sv: svtype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        begin
          PosMetaGenCanonical(cpcpos, gms);
          with gms do
            for index := 0 to movecount - 1 do
              begin
                PosExecute(cpcpos, moves[index]);
                sv := TbWranglerProbe(sscptrvec[0]^.tbwrangler, cpcpos); {TBD}
                if not IsSvBroken(sv) then
                  WriteStrNL(ofile, MoveEncode(moves[index]) + ' ' + EncodeSv(CalcSvUp(sv)));
                PosRetract(cpcpos)
              end
        end
  end; { IcpDoCdtbm }

  procedure IcpDoCdtbs(var icp: icptype);
    var
      sv: svtype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        begin
          sv := TbWranglerProbe(sscptrvec[0]^.tbwrangler, cpcpos); {TBD}
          WriteStrNL(ofile, EncodeSv(sv))
        end
  end; { IcpDoCdtbs }

  procedure IcpDoCecho(var icp: icptype);
    var
      tokenptr: tokenptrtype;
      str: String;
  begin
    with icp, cpc do
      begin
        tokenptr := ctlist.head^.next;
        while tokenptr <> nil do
          begin
            str := tokenptr^.tstr;
            if IsStringQuoted(str) then
              WriteStr(ofile, '"' + str + '"')
            else
              WriteStr(ofile, str);
            tokenptr := tokenptr^.next;
            if tokenptr <> nil then
              WriteCh(ofile, ' ')
          end;
        WriteNL(ofile)
      end
  end; { IcpDoCecho }

  procedure IcpDoCefnormal(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 2) then
        IcpUserErrorTwoParms(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCefnormal }

  procedure IcpDoCexit(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        exiting := True
  end; { IcpDoCexit }

  procedure IcpDoCffmate(var icp: icptype);
    var
      t1ptr, t2ptr: tokenptrtype;
      nofault: Boolean;
      fenfile: Text;
      opened: Boolean;
      count: nctype;
      fmvc: Integer;
      epd: epdtype;
      str: String;
      altpos: postype;
      tasktimer: timertype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 2) then
        IcpUserErrorTwoParms(icp)
      else
        begin
          t1ptr := ctlist.head^.next;
          t2ptr := t1ptr^.next;
          if not IsStringUnsignedInteger(t2ptr^.tstr) then
            IcpUserError(icp, 'Second parameter must be an unsigned integer')
          else
            begin
              nofault := True;
              opened := False;
              PosInit(altpos);
              fmvc := DecodeUnsignedInteger(t2ptr^.tstr);
              Assign(fenfile, t1ptr^.tstr);
              if nofault then
                begin
                  Reset(fenfile);
                  if IOResult <> 0 then
                    begin
                      IcpUserError(icp, 'I/O fault: Reset failure');
                      nofault := False
                    end
                  else
                    opened := True;
                end;
              count := 0;
              TimerResetThenStart(tasktimer);

              repeat
                ReadLn(fenfile, str);
                PosDecode(altpos, str);
                SscReadySet(sscptrvec[0]^, cpcoptnset, altpos, mgmnotated); {TBD}
                SmokeyFindMate(sscptrvec[0]^, fmvc);
                if optntrea in cpcoptnset then
                  begin
                    EpdInit(epd);
                    EpdLoadFromSsc(epd, sscptrvec[0]^);
                    WritePrefix(ofile, 'ea');
                    WriteStrNL(ofile, EpdEncode(epd));
                    EpdTerm(epd)
                  end;
                Inc(count)
              until not nofault or eof(fenfile);

              TimerStop(tasktimer);
              if optntrts in cpcoptnset then
                begin
                  WritePrefix(ofile, 'ts');
                  WriteStrNL(ofile, EncodeCT(count, TimerCurrent(tasktimer)))
                end;
              if opened then
                Close(fenfile);
              PosTerm(altpos)
            end
        end
  end; { IcpDoCffmate }

  procedure IcpDoCffnormal(var icp: icptype);
    var
      t1ptr, t2ptr: tokenptrtype;
      count: nctype;
      str: String;
      nofault: Boolean;
      fenfile0, fenfile1: Text;
      opened0, opened1: Boolean;
      altpos: postype;
      tasktimer: timertype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 2) then
        IcpUserErrorTwoParms(icp)
      else
        begin
          nofault := True;
          opened0 := False;
          opened1 := False;
          t1ptr := ctlist.head^.next;
          t2ptr := t1ptr^.next;
          Assign(fenfile0, t1ptr^.tstr);
          Assign(fenfile1, t2ptr^.tstr);
          if nofault then
            begin
              Reset(fenfile0);
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Reset failure');
                  nofault := False
                end
              else
                opened0 := True;
            end;
          if nofault then
            begin
              Rewrite(fenfile1);
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Rewrite failure');
                  nofault := False
                end
              else
                opened1 := True;
            end;
          PosInit(altpos);
          TimerResetThenStart(tasktimer);
          count := 0;

          repeat
            ReadLn(fenfile0, str);
            PosDecode(altpos, str);
            WriteStrNL(fenfile1, PosEncode(altpos));
            Inc(count)
          until not nofault or eof(fenfile0);

          TimerStop(tasktimer);
          if optntrts in cpcoptnset then
            begin
              WritePrefix(ofile, 'ts');
              WriteStrNL(ofile, EncodeCT(count, TimerCurrent(tasktimer)))
            end;
          PosTerm(altpos);
          if opened0 then
            Close(fenfile0);
          if opened1 then
            Close(fenfile1);
        end
  end; { IcpDoCffnormal }

  procedure IcpDoCffperft(var icp: icptype);
    var
      t1ptr, t2ptr: tokenptrtype;
      nofault: Boolean;
      fenfile: Text;
      opened: Boolean;
      depth: Integer;
      sum, subsum: nctype;
      str: String;
      altpos: postype;
      tasktimer: timertype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 2) then
        IcpUserErrorTwoParms(icp)
      else
        begin
          t1ptr := ctlist.head^.next;
          t2ptr := t1ptr^.next;
          if not IsStringUnsignedInteger(t2ptr^.tstr) then
            IcpUserError(icp, 'Second parameter must be an unsigned integer')
          else
            begin
              nofault := True;
              opened := False;
              PosInit(altpos);
              depth := DecodeUnsignedInteger(t2ptr^.tstr);
              sum := 0;
              Assign(fenfile, t1ptr^.tstr);
              if nofault then
                begin
                  Reset(fenfile);
                  if IOResult <> 0 then
                    begin
                      IcpUserError(icp, 'I/O fault: Reset failure');
                      nofault := False
                    end
                  else
                    opened := True;
                end;
              TimerResetThenStart(tasktimer);

              repeat
                ReadLn(fenfile, str);
                PosDecode(altpos, str);
                subsum := PosPerftTran(altpos, ofile, depth, False);
                Inc(sum, subsum)
              until not nofault or eof(fenfile);

              TimerStop(tasktimer);
              if optntrts in cpcoptnset then
                begin
                  WritePrefix(ofile, 'ts');
                  WriteStrNL(ofile, EncodeCT(sum, TimerCurrent(tasktimer)))
                end;
              if opened then
                Close(fenfile);
              PosTerm(altpos)
            end
        end
  end; { IcpDoCffperft }

  procedure IcpDoCg(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        if PosHasNoMoves(cpcpos) then
          IcpUserError(icp, 'No moves available')
        else
          begin {TBD}
            SscReadySet(sscptrvec[0]^, cpcoptnset, cpcpos, mgmhyperdeluxe);
            SscSelect(sscptrvec[0]^);
            IcpPlayMove(icp, sscptrvec[0]^.predvar.usedlist.head^.move)
          end
  end; { IcpDoCg }

  procedure IcpDoCgg(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        while not PosIsGameOver(cpcpos) do
          begin {TBD}
            SscReadySet(sscptrvec[0]^, cpcoptnset, cpcpos, mgmhyperdeluxe);
            SscSelect(sscptrvec[0]^);
            IcpPlayMove(icp, sscptrvec[0]^.predvar.usedlist.head^.move)
          end
  end; { IcpDoCgg }

  procedure IcpDoChelp(var icp: icptype);
    var
      icpcindex: icpctype;
      optnindex: optntype;
      index: Integer;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        begin
          WriteStrNL(ofile, 'Enter a command, or a sequence of one or more SAN chess moves ');
          WriteNL(ofile);
          WriteStrNL(ofile, '  Commands:');
          for icpcindex := icpcmin to icpcmax do
            begin
              WriteStr(ofile, '    ' + icpcnames[icpcindex]);
              for index := Length(icpcnames[icpcindex]) to 10 do
                WriteCh(ofile, ' ');
              WriteStrNL(ofile, icpchelps[icpcindex])
            end;
          WriteNL(ofile);
          WriteStrNL(ofile, '  Options:');
          for optnindex := optnmin to optnmax do
            begin
              WriteStr(ofile, '    ' + optnnames[optnindex]);
              for index := Length(optnnames[optnindex]) to 10 do
                WriteCh(ofile, ' ');
              WriteStrNL(ofile, optnhelps[optnindex])
            end
        end
  end; { IcpDoChelp }

  procedure IcpDoCloadfen(var icp: icptype);
    var
      fenfile: Text;
      str: String;
      nofault: Boolean;
      opened: Boolean;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        begin
          nofault := True;
          opened := False;
          Assign(fenfile, ctlist.head^.next^.tstr);
          if nofault then
            begin
              Reset(fenfile);
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Reset failure');
                  nofault := False
                end
              else
                opened := True;
            end;
          if nofault then
            begin
              ReadLn(fenfile, str);
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Read failure');
                  nofault := False
                end
            end;
          if nofault then
            begin
              if not PosDecode(cpcpos, str) then
                begin
                  IcpUserError(icp, 'FEN data fault');
                  nofault := False;
                end
            end;
          if nofault then
            CpcSnycPgnGame(cpc);
          if opened then
            Close(fenfile)
        end
  end; { IcpDoCloadfen }

  procedure IcpDoCloadpgn(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCloadpgn }

  procedure IcpDoCmate(var icp: icptype);
  var
    tokenptr: tokenptrtype;
    fmvc0, fmvn1: Integer;
    epd: epdtype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        begin
          tokenptr := ctlist.head^.next;
          if not IsStringUnsignedInteger(tokenptr^.tstr) then
            IcpUserError(icp, 'Parameter must be an unsigned integer')
          else
            begin
              fmvc0 := DecodeUnsignedInteger(tokenptr^.tstr);
              if (fmvc0 < 1) or (fmvc0 >= (plylen div 2)) then
                IcpUserError(icp, 'Out of range')
              else
                if PosHasNoMoves(cpcpos) then
                  IcpUserError(icp, 'No moves')
                else
                  begin {TBD}
                    SscReadySet(sscptrvec[0]^, cpcoptnset, cpcpos, mgmnotated);
                    SmokeyFindMate(sscptrvec[0]^, fmvc0);
                    with sscptrvec[0]^ do
                      begin
                        if not IsSvMating(predsv) then
                          WriteStrNL(ofile, 'No mate found')
                        else
                          begin
                            fmvn1 := CalcMatingDistance(predsv);
                            WriteStrNL(ofile, 'Found mate in ' + EncodeInteger(fmvn1));
                            WriteStrNL(ofile, 'PV: ' + VariationPosEncode(predvar, cpcpos))
                          end;
                        if optntrts in cpcoptnset then
                          begin
                            WritePrefix(ofile, 'ts');
                            WriteStrNL(ofile, EncodeCT(nodecount, TimerCurrent(ssctimer)))
                          end;
                        if optntrea in cpcoptnset then
                          begin
                            EpdInit(epd);
                            EpdLoadFromSsc(epd, sscptrvec[0]^);
                            WritePrefix(ofile, 'ea');
                            WriteStrNL(ofile, EpdEncode(epd));
                            EpdTerm(epd)
                          end;
                      end
                  end
            end
        end
  end; { IcpDoCmate }

  procedure IcpDoCmtperft(var icp: icptype);
    var
      tokenptr: tokenptrtype;
      limit: Integer;
      tasktimer: timertype;
      nc: nctype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        begin
          tokenptr := ctlist.head^.next;
          if not IsStringUnsignedInteger(tokenptr^.tstr) then
            IcpUserError(icp, 'Parameter must be an unsigned integer')
          else
            begin
              limit := DecodeUnsignedInteger(tokenptr^.tstr);
              if limit < 1 then
                IcpUserError(icp, 'Parameter must be a positive integer')
              else
                begin
                  TimerResetThenStart(tasktimer);
                  nc := PosPerftTaskDriver(cpcpos, limit, True);
                  if optntrts in cpcoptnset then
                    begin
                      WritePrefix(ofile, 'ts');
                      WriteStrNL(ofile, EncodeCT(nc, TimerCurrent(tasktimer)))
                    end
                end
            end
        end
  end; { IcpDoCmtperft }

  procedure IcpDoCnew(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        CpcNewGame(cpc)
  end; { IcpDoCnew }

  procedure IcpDoCnoop(var icp: icptype);
  begin
  end; { IcpDoCnoop }

  procedure IcpDoCoptreset(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount < (1 + 1) then
        IcpUserErrorNeedAtLeastOneParm(icp)
      else
        if not OptnVerifyParameterList(ctlist) then
          IcpUserError(icp, 'Unrecognized option')
        else
          OptnSetAssignParameterList(cpcoptnset, ctlist, False)
  end; { IcpDoCoptreset }

  procedure IcpDoCoptset(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount < (1 + 1) then
        IcpUserErrorNeedAtLeastOneParm(icp)
      else
        if not OptnVerifyParameterList(ctlist) then
          IcpUserError(icp, 'Unrecognized option')
        else
          OptnSetAssignParameterList(cpcoptnset, ctlist, True)
  end; { IcpDoCoptset }

  procedure IcpDoCperftbulk(var icp: icptype);
  begin
    IcpPerft(icp, perftbulk)
  end; { IcpDoCperftbulk }

  procedure IcpDoCperftfull(var icp: icptype);
  begin
    IcpPerft(icp, perftfull)
  end; { IcpDoCperftfull }

  procedure IcpDoCperfttran(var icp: icptype);
  begin
    IcpPerft(icp, perfttran)
  end; { IcpDoCperfttran }

  procedure IcpDoCpfnormal(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 2) then
        IcpUserErrorTwoParms(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCpfnormal }

  procedure IcpDoCrg(var icp: icptype);
    var
      altpgngame: pgngametype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        begin
          PgnGameInit(altpgngame);
          PgnGameRandom(altpgngame, prng);
          WriteStr(ofile, PgnGameEncode(altpgngame));
          PgnGameTerm(altpgngame)
        end
  end; { IcpDoCrg }

  procedure IcpDoCrgdump(var icp: icptype);
    var
      t1ptr, t2ptr: tokenptrtype;
      index, limit: ui32type;
      pgnfile: Text;
      nofault: Boolean;
      opened: Boolean;
      altpgngame: pgngametype;
      tasktimer: timertype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 2) then
        IcpUserError(icp, 'Need exactly two parameters')
      else
        begin
          t1ptr := ctlist.head^.next;
          t2ptr := t1ptr^.next;
          if not IsStringUi32Type(t2ptr^.tstr) then
            IcpUserError(icp, 'Second parameter must be an unsigned integer')
          else
            begin
              nofault := True;
              opened := False;
              limit := DecodeUi32Type(t2ptr^.tstr);
              Assign(pgnfile, t1ptr^.tstr);
              if nofault then
                begin
                  Rewrite(pgnfile);
                  if IOResult <> 0 then
                    begin
                      IcpUserError(icp, 'I/O fault: Rewrite failure');
                      nofault := False
                    end
                  else
                    opened := True;
                end;
              PgnGameInit(altpgngame);
              TimerResetThenStart(tasktimer);
              index := 0;
              while nofault and (index < limit) do
                begin
                  PgnGameRandom(altpgngame, prng);
                  PgnGameTagSet(altpgngame, ptnround, EncodeLongInt(index + 1));
                  WriteStr(pgnfile, PgnGameEncode(altpgngame));
                  if IOResult <> 0 then
                    begin
                      IcpUserError(icp, 'I/O fault: Write failure');
                      nofault := False
                    end;
                  Inc(index)
                end;
              TimerStop(tasktimer);
              if optntrts in cpcoptnset then
                begin
                  WritePrefix(ofile, 'ts');
                  WriteStrNL(ofile, EncodeCT(limit, TimerCurrent(tasktimer)))
                end;
              PgnGameTerm(altpgngame);
              if opened then
                Close(pgnfile)
            end
        end
  end; { IcpDoCrgstat }

  procedure IcpDoCrgstat(var icp: icptype);
    var
      tokenptr: tokenptrtype;
      limit: ui32type;
      gtstats: gtstatstype;
      tasktimer: timertype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        begin
          tokenptr := ctlist.head^.next;
          if not IsStringUi32Type(tokenptr^.tstr) then
            IcpUserError(icp, 'Parameter must be an unsigned integer')
          else
            begin
              limit := DecodeUi32Type(tokenptr^.tstr);
              TimerResetThenStart(tasktimer);
              GtStatsFill(gtstats, prng, limit);
              TimerStop(tasktimer);
              WriteStr(ofile, GtStatsEncode(gtstats));
              if optntrts in cpcoptnset then
                begin
                  WritePrefix(ofile, 'ts');
                  WriteStrNL(ofile, EncodeCT(limit, TimerCurrent(tasktimer)))
                end
            end
        end
  end; { IcpDoCrgstat }

  procedure IcpDoCrm(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        if cpcpos.usedspevlist.ecount < 1 then
          IcpUserError(icp, 'No move to retract')
        else
          IcpUnplayMove(icp)
  end; { IcpDoCrm }

  procedure IcpDoCrmp(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        if cpcpos.usedspevlist.ecount < 2 then
          IcpUserError(icp, 'No move pair to retract')
        else
          begin
            IcpUnplayMove(icp);
            IcpUnplayMove(icp)
          end
  end; { IcpDoCrmp }

  procedure IcpDoCrmts(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        if cpcpos.usedspevlist.ecount = 0 then
          IcpUserError(icp, 'Already at starting position')
        else
          while cpcpos.usedspevlist.ecount > 0 do
            IcpUnplayMove(icp)
  end; { IcpDoCrmts }

  procedure IcpDoCs(var icp: icptype);
    var
      mc: mctype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        if PosHasNoMoves(cpcpos) then
          IcpUserError(icp, 'No moves available')
        else
          begin {TBD}
            SscReadySet(sscptrvec[0]^, cpcoptnset, cpcpos, mgmhyperdeluxe);
            SscSelect(sscptrvec[0]^);
            PosLoadToMc(cpcpos, mc);
            WriteStrNL(ofile, MoveEncodeMc(sscptrvec[0]^.predvar.usedlist.head^.move, mc))
          end
  end; { IcpDoCs }

  procedure IcpDoCsavefen(var icp: icptype);
    var
      fenfile: Text;
      nofault: Boolean;
      opened: Boolean;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        begin
          nofault := True;
          opened := False;
          Assign(fenfile, ctlist.head^.next^.tstr);
          if nofault then
            begin
              Rewrite(fenfile);
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Rewrite failure');
                  nofault := False
                end
              else
                opened := True;
            end;
          if nofault then
            begin
              WriteStrNL(fenfile, PosEncode(cpcpos));
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Write failure');
                  nofault := False
                end
            end;
          if opened then
            Close(fenfile)
        end
  end; { IcpDoCsavefen }

  procedure IcpDoCsavepgn(var icp: icptype);
    var
      pgnfile: Text;
      nofault: Boolean;
      opened: Boolean;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        begin
          nofault := True;
          opened := False;
          Assign(pgnfile, ctlist.head^.next^.tstr);
          if nofault then
            begin
              Rewrite(pgnfile);
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Rewrite failure');
                  nofault := False
                end
              else
                opened := True;
            end;
          if nofault then
            begin
              WriteStr(pgnfile, PgnGameEncode(pgngame));
              if IOResult <> 0 then
                begin
                  IcpUserError(icp, 'I/O fault: Write failure');
                  nofault := False
                end
            end;
          if opened then
            Close(pgnfile)
        end
  end; { IcpDoCsavepgn }

  procedure IcpDoCselftest(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        if SelfTest(ofile) then
          WriteStrNL(ofile, 'Passed')
        else
          WriteStrNL(ofile, 'Failed')
  end; { IcpDoCselftest }

  procedure IcpDoCsfen(var icp: icptype);
    var
      fenstr: String;
      tokenptr: tokenptrtype;
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 6) then
        IcpUserError(icp, 'Need exactly six parameters')
      else
        begin
          fenstr := '';
          tokenptr := ctlist.head^.next;
          while tokenptr <> nil do
            begin
              fenstr := fenstr + ' ' + tokenptr^.tstr;
              tokenptr := tokenptr^.next
            end;
          if not PosDecode(cpcpos, fenstr) then
            IcpUserError(icp, 'Invalid FEN data')
          else
            CpcSnycPgnGame(cpc)
        end
  end; { IcpDoCsfen }

  procedure IcpDoCslevfd(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCslevfd }

  procedure IcpDoCslevfn(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCslevfn }

  procedure IcpDoCslevft(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCslevft }

  procedure IcpDoCslevnt(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 1) then
        IcpUserErrorOneParm(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCslevnt }

  procedure IcpDoCslevut(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCslevut }

  procedure IcpDoCstag(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 2) then
        IcpUserErrorTwoParms(icp)
      else
        IcpUserError(icp, 'Not yet implemented')
  end; { IcpDoCstag }

  procedure IcpDoCtest(var icp: icptype);
  begin
  end; { IcpDoCtest }

  procedure IcpDoCttreset(var icp: icptype);
  begin
    with icp, cpc do
      if ctlist.ecount <> (1 + 0) then
        IcpUserErrorNoParms(icp)
      else
        SscTTReset(sscptrvec[0]^) {TBD}
  end; { IcpDoCttreset }

  procedure IcpDispatch(var icp: icptype);
  begin
    case icp.icpc of
      icpcbench:     IcpDoCbench(icp);
      icpcd:         IcpDoCd(icp);
      icpcdao:       IcpDoCdao(icp);
      icpcdb:        IcpDoCdb(icp);
      icpcdbbdb:     IcpDoCdbbdb(icp);
      icpcdbcolor:   IcpDoCdbcolor(icp);
      icpcdbmono:    IcpDoCdbmono(icp);
      icpcdesc:      IcpDoCdesc(icp);
      icpcdfen:      IcpDoCdfen(icp);
      icpcdm:        IcpDoCdm(icp);
      icpcdmsig:     IcpDoCdmsig(icp);
      icpcdobm:      IcpDoCdobm(icp);
      icpcdp:        IcpDoCdp(icp);
      icpcdpgn:      IcpDoCdpgn(icp);
      icpcdpi:       IcpDoCdpi(icp);
      icpcdps:       IcpDoCdps(icp);
      icpcdtbm:      IcpDoCdtbm(icp);
      icpcdtbs:      IcpDoCdtbs(icp);
      icpcecho:      IcpDoCecho(icp);
      icpcefnormal:  IcpDoCefnormal(icp);
      icpcexit:      IcpDoCexit(icp);
      icpcffmate:    IcpDoCffmate(icp);
      icpcffnormal:  IcpDoCffnormal(icp);
      icpcffperft:   IcpDoCffperft(icp);
      icpcg:         IcpDoCg(icp);
      icpcgg:        IcpDoCgg(icp);
      icpchelp:      IcpDoChelp(icp);
      icpcloadfen:   IcpDoCloadfen(icp);
      icpcloadpgn:   IcpDoCloadpgn(icp);
      icpcmate:      IcpDoCmate(icp);
      icpcmtperft:   IcpDoCmtperft(icp);
      icpcnew:       IcpDoCnew(icp);
      icpcnoop:      IcpDoCnoop(icp);
      icpcoptreset:  IcpDoCoptreset(icp);
      icpcoptset:    IcpDoCoptset(icp);
      icpcperftbulk: IcpDoCperftbulk(icp);
      icpcperftfull: IcpDoCperftfull(icp);
      icpcperfttran: IcpDoCperfttran(icp);
      icpcpfnormal:  IcpDoCpfnormal(icp);
      icpcrg:        IcpDoCrg(icp);
      icpcrgdump:    IcpDoCrgdump(icp);
      icpcrgstat:    IcpDoCrgstat(icp);
      icpcrm:        IcpDoCrm(icp);
      icpcrmp:       IcpDoCrmp(icp);
      icpcrmts:      IcpDoCrmts(icp);
      icpcs:         IcpDoCs(icp);
      icpcsavefen:   IcpDoCsavefen(icp);
      icpcsavepgn:   IcpDoCsavepgn(icp);
      icpcselftest:  IcpDoCselftest(icp);
      icpcsfen:      IcpDoCsfen(icp);
      icpcslevfd:    IcpDoCslevfd(icp);
      icpcslevfn:    IcpDoCslevfn(icp);
      icpcslevft:    IcpDoCslevft(icp);
      icpcslevnt:    IcpDoCslevnt(icp);
      icpcslevut:    IcpDoCslevut(icp);
      icpcstag:      IcpDoCstag(icp);
      icpctest:      IcpDoCtest(icp);
      icpcttreset:   IcpDoCttreset(icp)
    end { case }
  end; { IcpDispatch }

  procedure IcpHandleCommand(var icp: icptype);
    var
      str: String;
      tokenptr: tokenptrtype;
      move: movetype;

    function MatchIcpCommand(str: String): icpcxtype;
      var
        myresult: icpcxtype;
        b0, b1, probe: Integer;
    begin
      myresult := icpcnil;
      b0 := icpcmin;
      b1 := icpcmax;
      repeat
        probe := (b0 + b1) div 2;
        if str = icpcnames[probe] then
          myresult := icpctype(probe)
        else
          if str < icpcnames[probe] then
            b1 := probe - 1
          else
            b0 := probe + 1
      until (myresult <> icpcnil) or (b0 > b1);
      MatchIcpCommand := myresult
    end; { MatchIcpCommand }

  begin
    with icp, cpc do
      begin

        { Get a list of input tokens; this is the only console read/readln statement }

        WriteStr(ofile, '[] ');
        ReadLn(ifile, str);
        TokenListReset(ctlist);
        TokenListBuild(ctlist, str);

        { Continue on non empty input }

        if ctlist.ecount <> 0 then
          begin

            { Try command dispatch first }

            icpc := MatchIcpCommand(ctlist.head^.tstr);
            if icpc <> icpcnil then
              IcpDispatch(icp)
            else

              { Try user move sequence second }

              if not PosIsValidMoveTokenList(cpcpos, ctlist) then
                IcpUserError(icp, 'Invalid command/move(s); try "help" or "dm"')
              else
                begin
                  tokenptr := ctlist.head;
                  while tokenptr <> nil do
                    begin
                      PosMoveDecode(cpcpos, move, tokenptr^.tstr);
                      IcpPlayMove(icp, move);
                      tokenptr := tokenptr^.next
                    end
                end
          end
      end
  end; { IcpHandleCommand }

  procedure IcpCycle(var icp: icptype);
  begin
    with icp, cpc do
      repeat
        IcpHandleCommand(icp)
      until exiting
  end; { IcpCycle }

  procedure IcpInit(var icp: icptype);
  begin
    with icp do
      begin
        CpcInit(cpc);
        cpc.cpcoptnset := [optnadcp, optntrfv, optntrpv, optntrst, optntrts]
      end
  end; { IcpInit }

  procedure IcpTerm(var icp: icptype);
  begin
     with icp do
      CpcTerm(cpc)
  end; { IcpTerm }

  { ***** Simplified Chess Interface command processor routines ***** }

  procedure ScpInit(var scp: scptype);
  begin
    with scp do
      begin
        CpcInit(cpc)
        {TBD}
      end
  end; { ScpInit }

  procedure ScpTerm(var scp: scptype);
  begin
     with scp do
      begin
        CpcTerm(cpc)
        {TBD}
      end
  end; { ScpTerm }

  { ***** Initialization/termination routines ***** }

  procedure Initialize;

    procedure InitializePrngSubsystem;
      var
        prngslot: prngslottype;
    begin

      { Prime numbers }

      primes1vec[ 0] :=   2;
      primes1vec[ 1] :=   3;
      primes1vec[ 2] :=   5;
      primes1vec[ 3] :=   7;
      primes1vec[ 4] :=  11;
      primes1vec[ 5] :=  13;
      primes1vec[ 6] :=  17;
      primes1vec[ 7] :=  19;
      primes1vec[ 8] :=  23;
      primes1vec[ 9] :=  29;
      primes1vec[10] :=  31;
      primes1vec[11] :=  37;
      primes1vec[12] :=  41;
      primes1vec[13] :=  43;
      primes1vec[14] :=  47;
      primes1vec[15] :=  53;
      primes1vec[16] :=  59;
      primes1vec[17] :=  61;
      primes1vec[18] :=  67;
      primes1vec[19] :=  71;
      primes1vec[20] :=  73;
      primes1vec[21] :=  79;
      primes1vec[22] :=  83;
      primes1vec[23] :=  89;
      primes1vec[24] :=  97;
      primes1vec[25] := 101;
      primes1vec[26] := 103;
      primes1vec[27] := 107;
      primes1vec[28] := 109;
      primes1vec[29] := 113;
      primes1vec[30] := 127;

      { Prime numbers, doubled }

      for prngslot := prngslotmin to prngslotmax do
        primes2vec[prngslot] := primes1vec[prngslot] * 2

    end; { InitializePrngSubsystem }

    procedure InitializeBasicSubsystem;

      procedure InitializeBoardFileItems;
        var
          bfile: bfiletype;
      begin

        { Map board file to single ASCII character }

        for bfile := bfilemin to bfilemax do
          bfiletochar[bfile] := Char(Ord('a') + Ord(bfile));

        { Map board file to other file }

        for bfile := bfilemin to bfilemax do
          otherbfile[bfile] := bfiletype(bfilemax - Ord(bfile))

      end; { InitializeBoardFileItems }

      procedure InitializeBoardRankItems;
        var
          brank: branktype;
      begin

        { Map board rank to single ASCII character }

        for brank := brankmin to brankmax do
          branktochar[brank] := Char(Ord('1') + Ord(brank));

        { Map board rank to other rank }

        for brank := brankmin to brankmax do
          otherbrank[brank] := branktype(brankmax - Ord(brank));

        { Map color, board rank to White POV board rank }

        for brank := brankmin to brankmax do
          begin
            normalbrank[colorw, brank] := brank;
            normalbrank[colorb, brank] := otherbrank[brank]
          end;

        { Map en passant target rank to good color }

        epranktogood[brank1] := colorv;
        epranktogood[brank2] := colorv;
        epranktogood[brank3] := colorb;
        epranktogood[brank4] := colorv;
        epranktogood[brank5] := colorv;
        epranktogood[brank6] := colorw;
        epranktogood[brank7] := colorv;
        epranktogood[brank8] := colorv

      end; { InitializeBoardRankItems }

      procedure InitializeSquareItems;
        var
          sq: sqtype;
          bfile: bfiletype;
          brank: branktype;
      begin

        { Initialize the square to file vector }

        for sq := sqmin to sqmax do
          sqtobfile[sq] := bfiletype(Ord(sq) mod bfilelen);

        { Initialize the square to rank vector }

        for sq := sqmin to sqmax do
          sqtobrank[sq] := branktype(Ord(sq) div bfilelen);

        { Initialize the square to color vector }

        for sq := sqmin to sqmax do
          if Odd(Ord(sqtobfile[sq]) xor Ord(sqtobrank[sq])) then
            sqtocolor[sq] := colorw
          else
            sqtocolor[sq] := colorb;

        { Initialize the file and rank to square array }

        for bfile := bfilemin to bfilemax do
          for brank := brankmin to brankmax do
            bfilebranktosq[bfile, brank] := sqtype(Ord(bfile) + (Ord(brank) * bfilelen));

        { Initialize the reflect squares along x=0 vector }

        for sq := sqmin to sqmax do
          reflectx0[sq] := bfilebranktosq[otherbfile[sqtobfile[sq]], sqtobrank[sq]];

        { Initialize the reflect squares along y=0 vector }

        for sq := sqmin to sqmax do
          reflecty0[sq] := bfilebranktosq[sqtobfile[sq], otherbrank[sqtobrank[sq]]];

        { Initialize the reflect squares along x=y vector }

        for sq := sqmin to sqmax do
          reflectxy[sq] := bfilebranktosq[sqtobrank[sq], sqtobfile[sq]]

      end; { InitializeSquareItems }

      procedure InitializeDirectionItems;
      begin

        { Map direction to file delta }

        dirtobfiledelta[dire]   := dfde;
        dirtobfiledelta[dirn]   := dfdn;
        dirtobfiledelta[dirw]   := dfdw;
        dirtobfiledelta[dirs]   := dfds;
        dirtobfiledelta[dirne]  := dfdne;
        dirtobfiledelta[dirnw]  := dfdnw;
        dirtobfiledelta[dirsw]  := dfdsw;
        dirtobfiledelta[dirse]  := dfdse;
        dirtobfiledelta[direne] := dfdene;
        dirtobfiledelta[dirnne] := dfdnne;
        dirtobfiledelta[dirnnw] := dfdnnw;
        dirtobfiledelta[dirwnw] := dfdwnw;
        dirtobfiledelta[dirwsw] := dfdwsw;
        dirtobfiledelta[dirssw] := dfdssw;
        dirtobfiledelta[dirsse] := dfdsse;
        dirtobfiledelta[direse] := dfdese;

        { Map direction to rank delta }

        dirtobrankdelta[dire]   := drde;
        dirtobrankdelta[dirn]   := drdn;
        dirtobrankdelta[dirw]   := drdw;
        dirtobrankdelta[dirs]   := drds;
        dirtobrankdelta[dirne]  := drdne;
        dirtobrankdelta[dirnw]  := drdnw;
        dirtobrankdelta[dirsw]  := drdsw;
        dirtobrankdelta[dirse]  := drdse;
        dirtobrankdelta[direne] := drdene;
        dirtobrankdelta[dirnne] := drdnne;
        dirtobrankdelta[dirnnw] := drdnnw;
        dirtobrankdelta[dirwnw] := drdwnw;
        dirtobrankdelta[dirwsw] := drdwsw;
        dirtobrankdelta[dirssw] := drdssw;
        dirtobrankdelta[dirsse] := drdsse;
        dirtobrankdelta[direse] := drdese;

        { Map direction to square delta }

        dirtosqdelta[dire]   := dsde;
        dirtosqdelta[dirn]   := dsdn;
        dirtosqdelta[dirw]   := dsdw;
        dirtosqdelta[dirs]   := dsds;
        dirtosqdelta[dirne]  := dsdne;
        dirtosqdelta[dirnw]  := dsdnw;
        dirtosqdelta[dirsw]  := dsdsw;
        dirtosqdelta[dirse]  := dsdse;
        dirtosqdelta[direne] := dsdene;
        dirtosqdelta[dirnne] := dsdnne;
        dirtosqdelta[dirnnw] := dsdnnw;
        dirtosqdelta[dirwnw] := dsdwnw;
        dirtosqdelta[dirwsw] := dsdwsw;
        dirtosqdelta[dirssw] := dsdssw;
        dirtosqdelta[dirsse] := dsdsse;
        dirtosqdelta[direse] := dsdese;

        { Map direction to other direction }

        otherdir[dire]   := dirw;
        otherdir[dirn]   := dirs;
        otherdir[dirw]   := dire;
        otherdir[dirs]   := dirn;
        otherdir[dirne]  := dirsw;
        otherdir[dirnw]  := dirse;
        otherdir[dirsw]  := dirne;
        otherdir[dirse]  := dirnw;
        otherdir[direne] := dirwsw;
        otherdir[dirnne] := dirsse;
        otherdir[dirnnw] := dirssw;
        otherdir[dirwnw] := direse;
        otherdir[dirwsw] := direne;
        otherdir[dirssw] := dirnne;
        otherdir[dirsse] := dirnnw;
        otherdir[direse] := dirwnw;

        { Map sweep direction to bidirection }

        dirtobidir[dire]  := bidire;
        dirtobidir[dirn]  := bidirn;
        dirtobidir[dirw]  := bidire;
        dirtobidir[dirs]  := bidirn;
        dirtobidir[dirne] := bidirne;
        dirtobidir[dirnw] := bidirnw;
        dirtobidir[dirsw] := bidirne;
        dirtobidir[dirse] := bidirnw;

        { Direction selection sets }

        orthodirset := [orthodirmin..orthodirmax];
        diagodirset := [diagodirmin..diagodirmax];
        sweepdirset := [sweepdirmin..sweepdirmax];
        crookdirset := [crookdirmin..crookdirmax]

      end; { InitializeDirectionItems }

      procedure InitializeColorItems;
      begin

        { Map color to color name }

        colornames[colorw] := 'white';
        colornames[colorb] := 'black';

        { Map color to player name }

        playernames[colorw] := 'White';
        playernames[colorb] := 'Black';

        { Map color to single ASCII character }

        colortochar[colorw] := 'w';
        colortochar[colorb] := 'b';

        { Map color to other color }

        othercolor[colorw] := colorb;
        othercolor[colorb] := colorw;

        { Pawn advance directions by color }

        pawnadvdir[colorw] := dirn;
        pawnadvdir[colorb] := dirs;

        { Pawn retreat directions by color }

        pawnretdir[colorw] := dirs;
        pawnretdir[colorb] := dirn;

        { Castling avaliability masks by color }

        colortocavs[colorw] := [castwq, castwk];
        colortocavs[colorb] := [castbq, castbk];

        { First castling by color }

        colortocastling0[colorw] := castwq;
        colortocastling0[colorb] := castbq;

        { Final castling by color }

        colortocastling1[colorw] := castwk;
        colortocastling1[colorb] := castbk;

        { Synthesize a man by color }

        synthpawn[colorw] := manwp;
        synthpawn[colorb] := manbp;

        synthknight[colorw] := manwn;
        synthknight[colorb] := manbn;

        synthbishop[colorw] := manwb;
        synthbishop[colorb] := manbb;

        synthrook[colorw] := manwr;
        synthrook[colorb] := manbr;

        synthqueen[colorw] := manwq;
        synthqueen[colorb] := manbq;

        synthking[colorw] := manwk;
        synthking[colorb] := manbk

      end; { InitializeColorItems }

      procedure InitializePieceItems;
        var
          piece: piecertype;
      begin

        { Map piece to piece name }

        piecenames[piecep] := 'pawn';
        piecenames[piecen] := 'knight';
        piecenames[pieceb] := 'bishop';
        piecenames[piecer] := 'rook';
        piecenames[pieceq] := 'queen';
        piecenames[piecek] := 'king';

        { Map piece to single ASCII character }

        piecetochar[piecep] := 'P';
        piecetochar[piecen] := 'N';
        piecetochar[pieceb] := 'B';
        piecetochar[piecer] := 'R';
        piecetochar[pieceq] := 'Q';
        piecetochar[piecek] := 'K';

        { Map piece to score value }

        piecetosv[piecep] := svpvpawn;
        piecetosv[piecen] := svpvknight;
        piecetosv[pieceb] := svpvbishop;
        piecetosv[piecer] := svpvrook;
        piecetosv[pieceq] := svpvqueen;
        piecetosv[piecek] := svpvking;
        piecetosv[piecev] := 0;

        { Map piece to one side material signature delta }

        for piece := piecermin to piecermax do
          osmsigdeltavec[piece] := ui32type(1) shl (piece * 4)

      end; { InitializePieceItems }

      procedure InitializeColorPieceItems;
        var
          color: colorrtype;
      begin

        { Map color/piece to man }

        for color := colorrmin to colorrmax do
          begin
            colorpiecetoman[color, piecep] := synthpawn[color];
            colorpiecetoman[color, piecen] := synthknight[color];
            colorpiecetoman[color, pieceb] := synthbishop[color];
            colorpiecetoman[color, piecer] := synthrook[color];
            colorpiecetoman[color, pieceq] := synthqueen[color];
            colorpiecetoman[color, piecek] := synthking[color]
          end

      end; { InitializeColorPieceItems }

      procedure InitializeManItems;
        var
          man: mantype;
      begin

        { Map man to single ASCII character }

        mantochar[manwp] := 'P';
        mantochar[manwn] := 'N';
        mantochar[manwb] := 'B';
        mantochar[manwr] := 'R';
        mantochar[manwq] := 'Q';
        mantochar[manwk] := 'K';

        mantochar[manbp] := 'p';
        mantochar[manbn] := 'n';
        mantochar[manbb] := 'b';
        mantochar[manbr] := 'r';
        mantochar[manbq] := 'q';
        mantochar[manbk] := 'k';

        { Map man to color }

        mantocolor[manwp] := colorw;
        mantocolor[manwn] := colorw;
        mantocolor[manwb] := colorw;
        mantocolor[manwr] := colorw;
        mantocolor[manwq] := colorw;
        mantocolor[manwk] := colorw;

        mantocolor[manbp] := colorb;
        mantocolor[manbn] := colorb;
        mantocolor[manbb] := colorb;
        mantocolor[manbr] := colorb;
        mantocolor[manbq] := colorb;
        mantocolor[manbk] := colorb;

        mantocolor[manvv] := colorv;

        { Map man to piece }

        mantopiece[manwp] := piecep;
        mantopiece[manwn] := piecen;
        mantopiece[manwb] := pieceb;
        mantopiece[manwr] := piecer;
        mantopiece[manwq] := pieceq;
        mantopiece[manwk] := piecek;

        mantopiece[manbp] := piecep;
        mantopiece[manbn] := piecen;
        mantopiece[manbb] := pieceb;
        mantopiece[manbr] := piecer;
        mantopiece[manbq] := pieceq;
        mantopiece[manbk] := piecek;

        mantopiece[manvv] := piecev;

        { Map man to other man }

        for man := manrmin to manrmax do
          otherman[man] := colorpiecetoman[othercolor[mantocolor[man]], mantopiece[man]];
        otherman[manvv] := manvv;

        { Map man to string }

        for man := manrmin to manrmax do
          mannames[man] := colornames[mantocolor[man]] + ' ' + piecenames[mantopiece[man]];

        { Map man to score value }

        for man := manmin to manmax do
          mantosv[man] := piecetosv[mantopiece[man]];

        { Map man to first attack direction }

        mantodir0[manwp] := dirne;
        mantodir0[manwn] := crookdirmin;
        mantodir0[manwb] := diagodirmin;
        mantodir0[manwr] := orthodirmin;
        mantodir0[manwq] := sweepdirmin;
        mantodir0[manwk] := sweepdirmin;

        mantodir0[manbp] := dirsw;
        mantodir0[manbn] := crookdirmin;
        mantodir0[manbb] := diagodirmin;
        mantodir0[manbr] := orthodirmin;
        mantodir0[manbq] := sweepdirmin;
        mantodir0[manbk] := sweepdirmin;

        { Map man to last attack direction }

        mantodir1[manwp] := dirnw;
        mantodir1[manwn] := crookdirmax;
        mantodir1[manwb] := diagodirmax;
        mantodir1[manwr] := orthodirmax;
        mantodir1[manwq] := sweepdirmax;
        mantodir1[manwk] := sweepdirmax;

        mantodir1[manbp] := dirse;
        mantodir1[manbn] := crookdirmax;
        mantodir1[manbb] := diagodirmax;
        mantodir1[manbr] := orthodirmax;
        mantodir1[manbq] := sweepdirmax;
        mantodir1[manbk] := sweepdirmax;

        { Map man to material signature delta }

        for man := manrmin to manrmax do
          msigdeltavec[man] := ui64type(1) shl (man * 4);

        { Map man to pawn/king status }

        pawnmanset := [manwp, manbp];
        kingmanset := [manwk, manbk];

        { Map man to sweeper status }

        sweepermanset := [manwb, manwr, manwq, manbb, manbr, manbq];

        { Map color and sweep direction to sets of incoming attacking men (adjacent squares)}

        manatk0setvec[colorw, dire] := [manwr, manwq, manwk];
        manatk0setvec[colorw, dirn] := [manwr, manwq, manwk];
        manatk0setvec[colorw, dirw] := [manwr, manwq, manwk];
        manatk0setvec[colorw, dirs] := [manwr, manwq, manwk];

        manatk0setvec[colorw, dirne] := [manwb, manwq, manwk];
        manatk0setvec[colorw, dirnw] := [manwb, manwq, manwk];
        manatk0setvec[colorw, dirsw] := [manwp, manwb, manwq, manwk];
        manatk0setvec[colorw, dirse] := [manwp, manwb, manwq, manwk];

        manatk0setvec[colorb, dire] := [manbr, manbq, manbk];
        manatk0setvec[colorb, dirn] := [manbr, manbq, manbk];
        manatk0setvec[colorb, dirw] := [manbr, manbq, manbk];
        manatk0setvec[colorb, dirs] := [manbr, manbq, manbk];

        manatk0setvec[colorb, dirne] := [manbp, manbb, manbq, manbk];
        manatk0setvec[colorb, dirnw] := [manbp, manbb, manbq, manbk];
        manatk0setvec[colorb, dirsw] := [manbb, manbq, manbk];
        manatk0setvec[colorb, dirse] := [manbb, manbq, manbk];

        { Map color and sweep direction to sets of incoming attacking men (non adjacent squares)}

        manatk1setvec[colorw, dire] := [manwr, manwq];
        manatk1setvec[colorw, dirn] := [manwr, manwq];
        manatk1setvec[colorw, dirw] := [manwr, manwq];
        manatk1setvec[colorw, dire] := [manwr, manwq];

        manatk1setvec[colorw, dirne] := [manwb, manwq];
        manatk1setvec[colorw, dirnw] := [manwb, manwq];
        manatk1setvec[colorw, dirsw] := [manwb, manwq];
        manatk1setvec[colorw, dirse] := [manwb, manwq];

        manatk1setvec[colorb, dire] := [manbr, manbq];
        manatk1setvec[colorb, dirn] := [manbr, manbq];
        manatk1setvec[colorb, dirw] := [manbr, manbq];
        manatk1setvec[colorb, dire] := [manbr, manbq];

        manatk1setvec[colorb, dirne] := [manbb, manbq];
        manatk1setvec[colorb, dirnw] := [manbb, manbq];
        manatk1setvec[colorb, dirsw] := [manbb, manbq];
        manatk1setvec[colorb, dirse] := [manbb, manbq]

      end; { InitializeManItems }

      procedure InitializeMscItems;
      begin

        { Map move special case to promoted piece }

        msctopiece[mscreg] := piecev;
        msctopiece[mscepc] := piecev;
        msctopiece[msccqs] := piecev;
        msctopiece[msccks] := piecev;
        msctopiece[mscppn] := piecen;
        msctopiece[mscppb] := pieceb;
        msctopiece[mscppr] := piecer;
        msctopiece[mscppq] := pieceq;

        { Map move special case to additianal gain score }

        msctogain[mscreg] := 0;
        msctogain[mscepc] := svpvpawn;
        msctogain[msccqs] := 0;
        msctogain[msccks] := 0;
        msctogain[mscppn] := svpvknight - svpvpawn;
        msctogain[mscppb] := svpvbishop - svpvpawn;
        msctogain[mscppr] := svpvrook   - svpvpawn;
        msctogain[mscppq] := svpvqueen  - svpvpawn;

        { Map move special case to gainer status }

        gainmscset := [mscepc, mscppn, mscppb, mscppr, mscppq];

        { Map move special case to promotion status }

        prommscset := [mscppn, mscppb, mscppr, mscppq]

      end; { InitializeMscItems }

      procedure InitializeMfItems;
      begin

        { Map move flag to name }

        mfnames[mfandf] := 'andf';
        mfnames[mfandr] := 'andr';
        mfnames[mfbook] := 'book';
        mfnames[mfcert] := 'cert';
        mfnames[mfchck] := 'chck';
        mfnames[mfchmt] := 'chmt';
        mfnames[mfdraw] := 'draw';
        mfnames[mfdrfm] := 'drfm';
        mfnames[mfdrim] := 'drim';
        mfnames[mfdrrp] := 'drrp';
        mfnames[mfdrsm] := 'drsm';
        mfnames[mfnote] := 'note';
        mfnames[mfnull] := 'null';
        mfnames[mfsrch] := 'srch';
        mfnames[mftbas] := 'tbas';
        mfnames[mfvoid] := 'void'

      end; { InitializeMfItems }

      procedure InitializeEscItems;
      begin

        { Initialize the evaluation score component names }

        escnames[escmobilitybishop] := 'mobilitybishop';
        escnames[escmobilityknight] := 'mobilityknight';
        escnames[escmobilityqueen]  := 'mobilityqueen';
        escnames[escmobilityrook]   := 'mobilityrook';
        escnames[escpawnbackward]   := 'pawnbackward';
        escnames[escpawnconnected]  := 'pawnconnected';
        escnames[escpawnisolated]   := 'pawnisolated';
        escnames[escpawnlocation]   := 'pawnlocation';
        escnames[escpawnmajority]   := 'pawnmajority';
        escnames[escpawnmultiple]   := 'pawnmultiple';
        escnames[escpawnpassed]     := 'pawnpassed';
        escnames[escsidetomove]     := 'sidetomove';

        { Initialize the evaluation score component values }

        escsvvec[escmobilitybishop] :=  +3000;
        escsvvec[escmobilityknight] :=  +4000;
        escsvvec[escmobilityqueen]  :=  +1000;
        escsvvec[escmobilityrook]   :=  +2000;
        escsvvec[escpawnbackward]   := -40000;
        escsvvec[escpawnconnected]  :=  +5000;
        escsvvec[escpawnisolated]   := -60000;
        escsvvec[escpawnlocation]   :=  +1000;
        escsvvec[escpawnmajority]   := +20000;
        escsvvec[escpawnmultiple]   := -80000;
        escsvvec[escpawnpassed]     :=  +4000;
        escsvvec[escsidetomove]     := +40000

      end; { InitializeEscItems }

      procedure InitializeStItems;
      begin

        { Map search termination to name }

        stnames[stallbadbutone] := 'All ply zero moves certain bad except one';
        stnames[stallcertain]   := 'All ply zero moves have certain scores';
        stnames[stforcedlose]   := 'Forced lose detected';
        stnames[stforcedmate]   := 'Forced mate detected';
        stnames[stlimitdepth]   := 'Depth limit encountered';
        stnames[stlimitnode]    := 'Node count limit encountered';
        stnames[stlimittime]    := 'Time limit encountered';
        stnames[stnomoves]      := 'No moves available (checkmate/stalemate)';
        stnames[stquickdraw]    := 'Quick draw detected';
        stnames[stquicklose]    := 'Quick lose detected';
        stnames[stquickmate]    := 'Quick mate detected';
        stnames[strandom]       := 'Random pick';
        stnames[stsingleton]    := 'Only one move';
        stnames[stsysmaxdepth]  := 'System maximum depth reached';
        stnames[stunterminated] := 'Search is not yet finished'

      end; { InitializeStItems }

      procedure InitializeGtItems;
      begin

        { Map game termination to name }

        gtnames[gtcheckmate]    := 'Checkmate';
        gtnames[gtfiftymoves]   := 'FiftyMoves';
        gtnames[gtinsufficient] := 'Insufficient';
        gtnames[gtrepetition]   := 'Repetition';
        gtnames[gtstalemate]    := 'Stalemate';
        gtnames[gtunterminated] := 'Unterminated';

        { Map good color and game termination to result }

        colorgttogr[colorw, gtcheckmate]    := grwinb;
        colorgttogr[colorw, gtfiftymoves]   := grdraw;
        colorgttogr[colorw, gtinsufficient] := grdraw;
        colorgttogr[colorw, gtrepetition]   := grdraw;
        colorgttogr[colorw, gtstalemate]    := grdraw;
        colorgttogr[colorw, gtunterminated] := grnone;

        colorgttogr[colorb, gtcheckmate]    := grwinw;
        colorgttogr[colorb, gtfiftymoves]   := grdraw;
        colorgttogr[colorb, gtinsufficient] := grdraw;
        colorgttogr[colorb, gtrepetition]   := grdraw;
        colorgttogr[colorb, gtstalemate]    := grdraw;
        colorgttogr[colorb, gtunterminated] := grnone

      end; { InitializeGtItems }

      procedure InitializeGrItems;
      begin

        { Map game result to name }

        grnames[grnone] := '*';
        grnames[grdraw] := '1/2-1/2';
        grnames[grwinw] := '1-0';
        grnames[grwinb] := '0-1';
        grnames[grdfor] := '0-0'

      end; { InitializeGrItems }

    begin
      InitializeBoardFileItems;
      InitializeBoardRankItems;
      InitializeSquareItems;
      InitializeDirectionItems;
      InitializeColorItems;
      InitializePieceItems;
      InitializeColorPieceItems;
      InitializeManItems;
      InitializeMscItems;
      InitializeMfItems;
      InitializeEscItems;
      InitializeStItems;
      InitializeGtItems;
      InitializeGrItems
    end; { InitializeBasicSubsystem }

    procedure InitializeDirectionalTables;

      procedure InitializeAdvance;
        var
          sq: sqtype;
          dir: dirtype;
      begin
        for sq := sqmin to sqmax do
          for dir := dirmin to dirmax do
            advance[sq, dir] := CalcAdvance(sq, dir)
      end; { InitializeAdvance }

      procedure InitializeOnBoard;
        var
          sq: sqtype;
          dir: dirtype;
          flag: Boolean; { Needed for compiler bug work-around }
      begin
        for sq := sqmin to sqmax do
          for dir := dirmin to dirmax do
            begin
              flag := advance[sq, dir] <> sqnil;
              onboard[sq, dir] := flag
            end
      end; { InitializeAdvance }

      procedure InitializeCompass;
        var
          frsq, tosq: sqtype;
      begin
        for frsq := sqmin to sqmax do
          for tosq := sqmin to sqmax do
            compass[frsq, tosq] := CalcCompass(frsq, tosq)
      end; { InitializeCompass }

      procedure InitializeShadows;
        var
          frsq, tosq: sqtype;
          dir: dirxtype;
      begin
        for frsq := sqmin to sqmax do
          for tosq := sqmin to sqmax do
            begin
              dir := compass[frsq, tosq];
              if IsDirxSweep(dir) then
                shadows[frsq, tosq] := advance[tosq, dir]
              else
                shadows[frsq, tosq] := sqnil
            end
      end; { InitializeShadows }

    begin
      InitializeAdvance;
      InitializeOnBoard;
      InitializeCompass;
      InitializeShadows
    end; { InitializeDirectionalTables }

    procedure InitializeSquareScanningSubsystem;
      var
        index: Integer;
        sq: sqtype;
        dir: sweepdirtype;

      procedure ResolveScanMapEntry(mysq: sqtype; mydir: sweepdirtype);
        var
          prevsq, scansq: sqxtype;
      begin
        if scanmap[mysq, mydir] < 0 then
          begin
            prevsq := advance[mysq, otherdir[mydir]];
            if prevsq = sqnil then
              begin
                scanmap[mysq, mydir] := index;
                scansq := mysq;
                repeat
                  scansq := advance[scansq, mydir];
                  scansqs[index] := scansq;
                  Inc(index)
                until scansq = sqnil
              end
            else
              begin
                ResolveScanMapEntry(prevsq, mydir);
                scanmap[mysq, mydir] := scanmap[prevsq, mydir] + 1
              end
          end
      end; { ResolveScanMapEntry }

    begin
      index := 0;
      for sq := sqmin to sqmax do
        for dir := sweepdirmin to sweepdirmax do
          scanmap[sq, dir] := -1;
      for sq := sqmin to sqmax do
        for dir := sweepdirmin to sweepdirmax do
          ResolveScanMapEntry(sq, dir)
    end; { InitializeSquareScanningSubsystem }

    procedure InitializeBitboardSubsystem;

      procedure InitializeBitCountVec;
        var
          bbwspan: bbwspantype;
          bitindex: Integer;
      begin
        for bbwspan := bbwspanmin to bbwspanmax do
          begin
            bitcountvec[bbwspan] := 0;
            for bitindex := bbwbitmin to bbwbitmax do
              if Odd(bbwspan shr bitindex) then
                Inc(bitcountvec[bbwspan])
          end
      end; { InitializeBitCountVec }

      procedure InitializeBitFirstVec;
        var
          bbwspan: bbwspantype;
          bitindex: Integer;
      begin
        for bbwspan := bbwspanmin to bbwspanmax do
          begin
            bitfirstvec[bbwspan] := -1;
            bitindex := 0;
            while (bitfirstvec[bbwspan] < 0) and (bitindex < bbwbitlen) do
              if Odd(bbwspan shr bitindex) then
                bitfirstvec[bbwspan] := bitindex
              else
                Inc(bitindex)
          end
      end; { InitializeBitFirstVec }

      procedure InitializeConstantBitboards;
        var
          bbwindex: Integer;
          frsq: sqtype;
          tosq: sqxtype;
          bfile: bfiletype;
          brank: branktype;
          flank: flanktype;
          homes: homestype;
          color: colorrtype;
          man: manrtype;
          dir0, dir1: dirtype;
          dir: dirxtype;
      begin

        { Initialize the single bit bitboard vector; needed for most other bitboard operations }

        for frsq := sqmin to sqmax do
          begin
            BbReset(singlebitbbvec[frsq]);
            bbwindex := Ord(frsq) div bbwbitlen;
            singlebitbbvec[frsq].wvec[bbwindex] := 1 shl (Ord(frsq) mod bbwbitlen)
          end;

        { Initialize the cancel bit bitboard vector }

        for frsq := sqmin to sqmax do
          BbNot1(cancelbitbbvec[frsq], singlebitbbvec[frsq]);

        { Initialize the double bit bitboard vector }

        for frsq := sqmin to sqmax do
          for tosq := sqmin to sqmax do
            BbIor2(doublebitbbvec[frsq, tosq], singlebitbbvec[frsq], singlebitbbvec[tosq]);

        { Initialize the bermuda triangle bitboard }

        BbReset(bermudabb);
        for frsq := sqmin to sqmax do
          if sqtobrank[frsq] > sqtobfile[frsq] then
            BbSetSq(bermudabb, frsq);

        { Initialize the file bitboard vector }

        for bfile := bfilemin to bfilemax do
          begin
            BbReset(bfilebbvec[bfile]);
            for brank := bfilemin to bfilemax do
              BbSetSq(bfilebbvec[bfile], bfilebranktosq[bfile, brank])
          end;

        { Initialize the rank bitboard vector }

        for brank := brankmin to brankmax do
          begin
            BbReset(brankbbvec[brank]);
            for bfile := bfilemin to bfilemax do
              BbSetSq(brankbbvec[brank], bfilebranktosq[bfile, brank])
          end;

        { Initialize the flank bitboard vector }

        for flank := flankmax to flankmax do
          BbReset(flankbbvec[flank]);
        for bfile := bfilea to bfiled do
          BbIor2D(flankbbvec[flankq], bfilebbvec[bfile]);
        for bfile := bfilee to bfileh do
          BbIor2D(flankbbvec[flankk], bfilebbvec[bfile]);

        { Initialize the home side bitboard vector }

        for homes := homesmin to homesmax do
          BbReset(homesbbvec[homes]);
        for brank := brank1 to brank4 do
          BbIor2D(homesbbvec[homesw], brankbbvec[brank]);
        for brank := brank5 to brank8 do
          BbIor2D(homesbbvec[homesb], brankbbvec[brank]);

        { Initialize the quadrant bitboard vector }

        BbAnd2(quadbbvec[quadwq], homesbbvec[homesw], flankbbvec[flankq]);
        BbAnd2(quadbbvec[quadwk], homesbbvec[homesw], flankbbvec[flankk]);
        BbAnd2(quadbbvec[quadbq], homesbbvec[homesb], flankbbvec[flankq]);
        BbAnd2(quadbbvec[quadbk], homesbbvec[homesb], flankbbvec[flankk]);

        { Initialize the edge bitboard vector }

        edgebbvec[dire] := bfilebbvec[bfileh];
        edgebbvec[dirn] := brankbbvec[brank8];
        edgebbvec[dirw] := bfilebbvec[bfilea];
        edgebbvec[dirs] := brankbbvec[brank1];

        BbIor2(edgebbvec[dirne], edgebbvec[dirn], edgebbvec[dire]);
        BbIor2(edgebbvec[dirnw], edgebbvec[dirn], edgebbvec[dirw]);
        BbIor2(edgebbvec[dirsw], edgebbvec[dirs], edgebbvec[dirw]);
        BbIor2(edgebbvec[dirse], edgebbvec[dirs], edgebbvec[dire]);

        { Initialize the pawn attack-to-squares bitboard vector }

        for color := colorrmin to colorrmax do
          begin
            man := synthpawn[color];
            dir0 := mantodir0[man];
            dir1 := mantodir1[man];
            for frsq := sqmin to sqmax do
              begin
                BbReset(pawnatkbbvec[color, frsq]);
                for dir := dir0 to dir1 do
                  begin
                    tosq := advance[frsq, dir];
                    if tosq <> sqnil then
                      BbSetSq(pawnatkbbvec[color, frsq], tosq)
                  end
              end
          end;

        { Initialize the knight attack-to-squares bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            BbReset(knightatkbbvec[frsq]);
            for dir := crookdirmin to crookdirmax do
              begin
                tosq := advance[frsq, dir];
                if tosq <> sqnil then
                  BbSetSq(knightatkbbvec[frsq], tosq)
              end
          end;

        { Initialize the king attack-to-squares bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            BbReset(kingatkbbvec[frsq]);
            for dir := sweepdirmin to sweepdirmax do
              begin
                tosq := advance[frsq, dir];
                if tosq <> sqnil then
                  BbSetSq(kingatkbbvec[frsq], tosq)
              end
          end;

        { Initialize the open ray bitboard vector }

        for frsq := sqmin to sqmax do
          for dir := sweepdirmin to sweepdirmax do
            begin
              BbReset(openraybbvec[frsq, dir]);
              tosq := frsq;
              repeat
                tosq := advance[tosq, dir];
                if tosq <> sqnil then
                  BbSetSq(openraybbvec[frsq, dir], tosq)
              until tosq = sqnil
            end;

        { Initialize the intersquare pathway bitboard vector }

        for frsq := sqmin to sqmax do
          for tosq := sqmin to sqmax do
            begin
              dir := compass[frsq, tosq];
              if IsDirxSweep(dir) then
                BbAnd2(
                    pathwaybbvec[frsq, tosq],
                    openraybbvec[frsq, dir],
                    openraybbvec[tosq, otherdir[dir]])
              else
                BbReset(pathwaybbvec[frsq, tosq])
            end;

        { Initialize the beam open ray bitboard vector }

        for frsq := sqmin to sqmax do
          for tosq := sqmin to sqmax do
            begin
              dir := compass[frsq, tosq];
              if IsDirxSweep(dir) then
                beambbvec[frsq, tosq] := openraybbvec[frsq, dir]
              else
                BbReset(beambbvec[frsq, tosq])
            end;

        { Initialize the orthogonal ray bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            BbReset(orthoraybbvec[frsq]);
            for dir := orthodirmin to orthodirmax do
              BbIor2D(orthoraybbvec[frsq], openraybbvec[frsq, dir])
          end;

        { Initialize the diagonal ray bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            BbReset(diagoraybbvec[frsq]);
            for dir := diagodirmin to diagodirmax do
              BbIor2D(diagoraybbvec[frsq], openraybbvec[frsq, dir])
          end;

        { Initialize the sweep ray bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            BbReset(sweepraybbvec[frsq]);
            for dir := sweepdirmin to sweepdirmax do
              BbIor2D(sweepraybbvec[frsq], openraybbvec[frsq, dir])
          end;

        { Initialize the lateral adjacent squares bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            BbReset(lateralbbvec[frsq]);
            tosq := advance[frsq, dire];
            if tosq <> sqnil then
              BbSetSq(lateralbbvec[frsq], tosq);
            tosq := advance[frsq, dirw];
            if tosq <> sqnil then
              BbSetSq(lateralbbvec[frsq], tosq)
          end;

        { Initialize the lateral adjacent file squares bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            BbReset(adjfilebbvec[frsq]);
            tosq := advance[frsq, dire];
            if tosq <> sqnil then
              BbIor2D(adjfilebbvec[frsq], bfilebbvec[sqtobfile[tosq]]);
            tosq := advance[frsq, dirw];
            if tosq <> sqnil then
              BbIor2D(adjfilebbvec[frsq], bfilebbvec[sqtobfile[tosq]])
          end;

        { Initialize the connected adjacent file squares bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            connectbbvec[frsq] := kingatkbbvec[frsq];
            BbAnd2C2D(connectbbvec[frsq], bfilebbvec[sqtobfile[frsq]])
          end;

        { Initialize the two/three file majority file squares bitboard vector }

        for frsq := sqmin to sqmax do
          begin
            majfilebbvec[frsq] := bfilebbvec[sqtobfile[frsq]];
            tosq := advance[frsq, dire];
            if tosq <> sqnil then
              BbIor2D(majfilebbvec[frsq], bfilebbvec[sqtobfile[tosq]]);
            tosq := advance[frsq, dirw];
            if tosq <> sqnil then
              BbIor2D(majfilebbvec[frsq], bfilebbvec[sqtobfile[tosq]])
          end;

        { Initialize the actual/potental pawn guard mask squares bitboard vector }

        for color := colorrmin to colorrmax do
          begin
            dir := pawnretdir[color];
            for frsq := sqmin to sqmax do
              begin
                guardedbbvec[color, frsq] := lateralbbvec[frsq];
                tosq := advance[frsq, dire];
                if tosq <> sqnil then
                  BbIor2D(guardedbbvec[color, frsq], openraybbvec[tosq, dir]);
                tosq := advance[frsq, dirw];
                if tosq <> sqnil then
                  BbIor2D(guardedbbvec[color, frsq], openraybbvec[tosq, dir])
              end
            end;

        { Initialize the pawn forward track bitboard vector }

        for color := colorrmin to colorrmax do
          begin
            dir := pawnadvdir[color];
            for frsq := sqmin to sqmax do
              ptrackbbvec[color, frsq] := openraybbvec[frsq, dir]
          end;

        { Initialize the passed pawn forward test square bitboard vector }

        for color := colorrmin to colorrmax do
          begin
            man := synthpawn[color];
            dir0 := mantodir0[man];
            dir1 := mantodir1[man];
            for frsq := sqmin to sqmax do
              begin
                passerbbvec[color, frsq] := ptrackbbvec[color, frsq];
                tosq := advance[frsq, dir0];
                if tosq <> sqnil then
                  BbIor2D(passerbbvec[color, frsq], ptrackbbvec[color, tosq]);
                tosq := advance[frsq, dir1];
                if tosq <> sqnil then
                  BbIor2D(passerbbvec[color, frsq], ptrackbbvec[color, tosq])
              end
          end

      end; { InitializeConstantBitboards }

    begin
      InitializeBitCountVec;
      InitializeBitFirstVec;
      InitializeConstantBitboards
    end; { InitializeBitboardSubsystem }

    procedure InitializeAttackCounts;
      var
        color: colorrtype;
        sq: sqtype;
    begin

      { Initialize pawn attack counts }

      for color := colorrmin to colorrmax do
        for sq := sqmin to sqmax do
          pawnatkccvec[color, sq] := BbCount(pawnatkbbvec[color, sq]);

      { Initialize knight attack counts }

      for sq := sqmin to sqmax do
        knightatkccvec[sq] := BbCount(knightatkbbvec[sq]);

      { Initialize king attack counts }

      for sq := sqmin to sqmax do
        kingatkccvec[sq] := BbCount(kingatkbbvec[sq])

    end; { InitializeAttackCounts }

    procedure InitializeHashSubsystem;
      var
        prng: prngtype;

      procedure HashCreate(var hash: hashtype);
        var
          bitindex: Integer;
      begin
        with hash do
          begin
            bits0 := 0;
            for bitindex := sqmin to sqmax do
              bits0 := (bits0 shl 1) or PrngNextBit(prng);
            bits1 := 0;
            for bitindex := sqmin to sqmax do
              bits1 := (bits1 shl 1) or PrngNextBit(prng)
          end
      end; { InitializeHash }

      procedure InitializeHashManSqVec;
        var
          man: manrtype;
          sq: sqtype;
      begin
        for man := manrmin to manrmax do
          for sq := sqmin to sqmax do
            HashCreate(hashmansqvec[man, sq])
      end; { InitializeHashManSqVec }

      procedure InitializeHashCastlingVec;
        var
          cast: casttype;
      begin
        for cast := castmin to castmax do
          HashCreate(hashcastlingvec[cast])
      end; { InitializeHashCastlingVec }

      procedure InitializeHashEpFileVec;
        var
          bfile: bfiletype;
      begin
        for bfile := bfilemin to bfilemax do
          HashCreate(hashepfilevec[bfile])
      end; { InitializeHashEpFileVec }

    begin
      PrngReset(prng);
      InitializeHashManSqVec;
      InitializeHashCastlingVec;
      InitializeHashEpFileVec
    end; { InitializeHashSubsystem }

    procedure InitializeCastlingSubsystem;

      procedure SetCdr(
          cast: casttype;
          ch: Char; color: colorrtype; f0, f1, f2, f3: bfiletype; msc: msctype);
        var
          brank: branktype;
      begin
        with cdrvec[cast] do
          begin
            brank := normalbrank[color, brank1];
            cmsc := msc;
            cach := ch;
            karc := color;
            k0sq := bfilebranktosq[f0, brank];
            k1sq := bfilebranktosq[f1, brank];
            r0sq := bfilebranktosq[f2, brank];
            r1sq := bfilebranktosq[f3, brank];
            kman := synthking[color];
            rman := synthrook[color];
            cabb := pathwaybbvec[k0sq, k1sq];
            BbSetSq(cabb, k0sq);
            BbSetSq(cabb, k1sq);
            cvbb := pathwaybbvec[k0sq, r0sq];
            MoveSynthM4(cmov, k0sq, k1sq, kman, cmsc)
          end
      end; { SetCdr }

    begin
      SetCdr(castwq, 'Q', colorw, bfilee, bfilec, bfilea, bfiled, msccqs);
      SetCdr(castwk, 'K', colorw, bfilee, bfileg, bfileh, bfilef, msccks);
      SetCdr(castbq, 'q', colorb, bfilee, bfilec, bfilea, bfiled, msccqs);
      SetCdr(castbk, 'k', colorb, bfilee, bfileg, bfileh, bfilef, msccks)
    end; { InitializeCastlingSubsystem }

    procedure InitializeEpdSubsystem;
    begin
      {TBD}
    end; { InitializeEpdSubsystem }

    procedure InitializePgnSubsystem;
    begin

      { Initialize the PGN tag names }

      ptnnames[ptnevent]       := 'Event';
      ptnnames[ptnsite]        := 'Site';
      ptnnames[ptndate]        := 'Date';
      ptnnames[ptnwhite]       := 'White';
      ptnnames[ptnblack]       := 'Black';
      ptnnames[ptnround]       := 'Round';
      ptnnames[ptnresult]      := 'Result';
      ptnnames[ptnfen]         := 'FEN';
      ptnnames[ptntime]        := 'Time';
      ptnnames[ptnendfen]      := 'EndFEN';
      ptnnames[ptntermination] := 'Termination';
      ptnnames[ptnplycount]    := 'PlyCount';
      ptnnames[ptnutc]         := 'UTC'

    end; { InitializePgnSubsystem }

    procedure InitializeTablebaseSubsystem;

      procedure InitializeTablebaseDescriptorVector;
        var
          tbcindex: Integer;
          tbm: tbmtype;

        procedure GenerateEntryGroup;
          var
            index: Integer;
            mancountvec: array [colorrtype] of Integer;

          procedure GenerateEntrySubGroup;
            var
              scanosmsigvec, baseosmsigvec: osmsigvectype;

            procedure AddEntry;
              const
                tbdirpath = 'TB';

              var
                wpc, bpc: Integer;
            begin
              with tbdrvec[tbcindex] do
                begin
                  tbc := tbcindex;
                  osmsigvec := scanosmsigvec;
                  MsigLoadFromOsMsigVec(msig, osmsigvec);
                  mancount := MsigCount(msig);
                  mcvec[colorw] := mancountvec[colorw];
                  mcvec[colorb] := mancountvec[colorb];
                  name := MsigName(msig);
                  wpc := MsigCountMan(msig, manwp);
                  bpc := MsigCountMan(msig, manbp);
                  epflag := (wpc > 0) and (bpc > 0);
                  if (wpc > 0) or (bpc > 0) then
                    begin
                      fold := fold32;
                      if bpc > 0 then
                        foldslot := mancount - 1
                      else
                        foldslot := mancount - mcvec[colorb] - 1
                    end
                  else
                    begin
                      fold := fold10;
                      foldslot := mancount - 1
                    end;
                  fnvec[colorw] := tbdirpath + '/' + name + '.tbw';
                  fnvec[colorb] := tbdirpath + '/' + name + '.tbb'
                end;
              Inc(tbcindex)
            end; { AddEntry }

            procedure InitScan;
              var
                color: colorrtype;
            begin
              for color := colorrmin to colorrmax do
                begin
                  baseosmsigvec[color] := 0;
                  Inc(baseosmsigvec[color], osmsigdeltavec[piecek]);
                  Inc(baseosmsigvec[color], (osmsigdeltavec[piecep] * (mancountvec[color] - 1)))
                end;
              scanosmsigvec := baseosmsigvec
            end; { InitScan }

            procedure NextScan;

              procedure NextScanColor(color: colorrtype);
                var
                  piece, subpiece: piecetype;
                  pawncount: Integer;
              begin
                piece := OsMsigFirstPiece(scanosmsigvec[color]);
                if piece <> piecek then
                  if piece = pieceq then
                    scanosmsigvec[color] := baseosmsigvec[color]
                  else
                    begin
                      pawncount := -1;
                      for subpiece := piecep to piece do
                        begin
                          Inc(pawncount, OsMsigCountPiece(scanosmsigvec[color], subpiece));
                          OsMsigClearPiece(scanosmsigvec[color], subpiece)
                        end;
                      Inc(scanosmsigvec[color], (pawncount * osmsigdeltavec[piecep]));
                      Inc(scanosmsigvec[color], osmsigdeltavec[piece + 1])
                    end
              end; { NextScanColor }

            begin
              NextScanColor(colorb);
              if (mancountvec[colorw] = mancountvec[colorb]) and
                  (scanosmsigvec[colorb] > scanosmsigvec[colorw]) then
                scanosmsigvec[colorb] := baseosmsigvec[colorb];
              if scanosmsigvec[colorb] = baseosmsigvec[colorb] then
                NextScanColor(colorw)
            end; { NextScan }

          begin
            InitScan;
            repeat
              AddEntry;
              NextScan
            until OsMsigVecEqual(scanosmsigvec, baseosmsigvec)
          end; { GenerateEntrySubGroup }

        begin
          for index := tbm - (tbm div 2) to tbm - 1 do
            begin
              mancountvec[colorw] := index;
              mancountvec[colorb] := tbm - mancountvec[colorw];
              GenerateEntrySubGroup
            end
        end; { GenerateEntryGroup }

      begin
        tbcindex := 0;
        for tbm := tbmmin to tbmmax do
          GenerateEntryGroup;
        Assert(tbcindex = tbclen)
      end; { InitializeTablebaseDescriptorVector }

      procedure InitializeTablebaseSignatureVector;

        procedure LoadTablebaseSignatureVector;
          var
            mytbc: tbctype;
        begin
          for mytbc := tbcmin to tbcmax do
            begin
              with tbmsmvec[(mytbc * colorrlen) + colorw] do
                begin
                  tbc := mytbc;
                  msig := tbdrvec[mytbc].msig;
                  isrev := False
                end;
              with tbmsmvec[(mytbc * colorrlen) + colorb] do
                begin
                  tbc := mytbc;
                  msig := MsigCalcOther(tbdrvec[mytbc].msig);
                  isrev := True
                end
            end
        end; { LoadTablebaseSignatureVector }

        procedure SortTablebaseSignatureVector;
          var
            index: si32type;
            temptbmsms: array [tbcmstype] of tbmsmtype;
            altindex, saveindex: array [tbcmstype] of si32type;
            altmsig, savemsig: array [tbcmstype] of msigtype;

          procedure SortSignatureSegment(start: tbcmstype; count: si32type);
            var
              start0, start1: tbcmstype;
              count0, count1: si32type;
              tempindex: tbcmstype;
              tempmsig: msigtype;
              fill: si32type;
              pick0, pick1: si32type;
              pick0limit, pick1limit: si32type;
          begin
            if count > 1 then
              begin

                { At least two records need sorted }

                if count = 2 then
                  begin

                    { Sort two records }

                    if altmsig[start] > altmsig[start + 1] then
                      begin

                        { Simple exchange }

                        tempindex := altindex[start];
                        altindex[start] := altindex[start + 1];
                        altindex[start + 1] := tempindex;
                        tempmsig := altmsig[start];
                        altmsig[start] := altmsig[start + 1];
                        altmsig[start + 1] := tempmsig
                      end
                  end
                else
                  begin

                    { Sort more than two records; start with split calculation }

                    count0 := count div 2;
                    count1 := count - count0;
                    start0 := start;
                    start1 := start0 + count0;

                    { Sort the two segments }

                    SortSignatureSegment(start0, count0);
                    SortSignatureSegment(start1, count1);

                    { Set up to merge the results of two segments }

                    fill := start;
                    pick0 := start0;
                    pick1 := start1;
                    pick0limit := pick0 + count0;
                    pick1limit := pick1 + count1;

                    { Fill while at least one unpicked record in each segment }

                    while (pick0 < pick0limit) and (pick1 < pick1limit) do
                      begin
                        if altmsig[pick0] < altmsig[pick1] then
                          begin
                            savemsig[fill] := altmsig[pick0];
                            saveindex[fill] := altindex[pick0];
                            Inc(pick0)
                          end
                        else
                          begin
                            savemsig[fill] := altmsig[pick1];
                            saveindex[fill] := altindex[pick1];
                            Inc(pick1)
                          end;
                        Inc(fill)
                      end;

                    { Add any remaining records from the first segment }

                    while pick0 < pick0limit do
                      begin
                        savemsig[fill] := altmsig[pick0];
                        saveindex[fill] := altindex[pick0];
                        Inc(pick0);
                        Inc(fill)
                      end;

                    { Add any remaining records from the second segment }

                    while pick1 < pick1limit do
                      begin
                        savemsig[fill] := altmsig[pick1];
                        saveindex[fill] := altindex[pick1];
                        Inc(pick1);
                        Inc(fill)
                      end;

                    { Copy to result }

                    for fill := start to (start + count - 1) do
                      begin
                        altmsig[fill] := savemsig[fill];
                        altindex[fill] := saveindex[fill]
                      end
                  end
              end
          end; { SortSignatureSegment }

        begin
          if tbcmslen > 1 then
            begin
              for index := tbcmsmin to tbcmsmax do
                begin
                  temptbmsms[index] := tbmsmvec[index];
                  altindex[index] := index;
                  altmsig[index] := tbmsmvec[index].msig
                end;
              SortSignatureSegment(0, tbcmslen);
              for index := tbcmsmin to tbcmsmax do
                tbmsmvec[index] := temptbmsms[altindex[index]]
            end
        end; { SortTablebaseSignatureVector }

      begin
        LoadTablebaseSignatureVector;
        SortTablebaseSignatureVector
      end; { InitializeTablebaseSignatureVector }

      procedure InitializeFoldMaps;
        var
          sq: sqtype;
      begin

        { Initialize the fold mode 10 (triangle) map }

        for sq := sqmin to sqmax do
          fold10map[sq] := -1;

        fold10map[sqa1] := 0;
        fold10map[sqb1] := 1;
        fold10map[sqc1] := 2;
        fold10map[sqd1] := 3;
        fold10map[sqb2] := 4;
        fold10map[sqc2] := 5;
        fold10map[sqd2] := 6;
        fold10map[sqc3] := 7;
        fold10map[sqd3] := 8;
        fold10map[sqd4] := 9;

        { Initialize the fold mode 32 (flank) map }

        for sq := sqmin to sqmax do
          fold32map[sq] := -1;

        fold32map[sqa1] :=  0;
        fold32map[sqb1] :=  1;
        fold32map[sqc1] :=  2;
        fold32map[sqd1] :=  3;
        fold32map[sqa2] :=  4;
        fold32map[sqb2] :=  5;
        fold32map[sqc2] :=  6;
        fold32map[sqd2] :=  7;
        fold32map[sqa3] :=  8;
        fold32map[sqb3] :=  9;
        fold32map[sqc3] := 10;
        fold32map[sqd3] := 11;
        fold32map[sqa4] := 12;
        fold32map[sqb4] := 13;
        fold32map[sqc4] := 14;
        fold32map[sqd4] := 15;
        fold32map[sqa5] := 16;
        fold32map[sqb5] := 17;
        fold32map[sqc5] := 18;
        fold32map[sqd5] := 19;
        fold32map[sqa6] := 20;
        fold32map[sqb6] := 21;
        fold32map[sqc6] := 22;
        fold32map[sqd6] := 23;
        fold32map[sqa7] := 24;
        fold32map[sqb7] := 25;
        fold32map[sqc7] := 26;
        fold32map[sqd7] := 27;
        fold32map[sqa8] := 28;
        fold32map[sqb8] := 29;
        fold32map[sqc8] := 30;
        fold32map[sqd8] := 31

      end; { InitializeFoldMaps }

    begin
      InitializeTablebaseDescriptorVector;
      InitializeTablebaseSignatureVector;
      InitializeFoldMaps
    end; { InitializeTablebaseSubsystem }

    procedure InitializeSelfTestSubsystem;

      procedure SetStpr(index: Integer; myfen: fentype; t1, t2, t3: nctype);
      begin
        with stprvec[index] do
          begin
            fen := myfen;
            tvec[1] := t1;
            tvec[2] := t2;
            tvec[3] := t3
          end
      end; { SetStpr }

    begin

      { Initialize the self test perft data vector }

      SetStpr( 0, 'rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1',             20,  400,  8902);
      SetStpr( 1, '2qrr1n1/3b1kp1/2pBpn1p/1p2PP2/p2P4/1BP5/P3Q1PP/4RRK1 w - - 0 1',       44,  833, 35770);
      SetStpr( 2, 'r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq - 0 1', 48, 2039, 97862);
      SetStpr( 3, '8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1',                            14,  191,  2812);
      SetStpr( 4, 'r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1',      6,  264,  9467);
      SetStpr( 5, 'r2q1rk1/pP1p2pp/Q4n2/bbp1p3/Np6/1B3NBn/pPPP1PPP/R3K2R b KQ - 0 1',      6,  264,  9467);
      SetStpr( 6, 'rnbqkb1r/ppppp1pp/7n/4Pp2/8/8/PPPP1PPP/RNBQKBNR w KQkq f6 0 1',        31,  570, 17546);
      SetStpr( 7, '8/3k4/8/4b3/1p1p1p2/8/1PPRP2K/8 w - - 0 1',                            12,  197,  2696);
      SetStpr( 8, '8/4rP2/8/8/4pk2/8/3P2PP/4K2R w K - 0 1',                               17,  182,  3232);
      SetStpr( 9, 'rnb1kbnr/pp1ppppp/8/8/q1p4K/5P2/PPPPP1PP/RNBQ1BNR w kq - 2 5',         21,  607, 12644);
      SetStpr(10, 'rnbq1bnr/pppp1ppp/3kp3/3P4/1B6/8/PPP1PPPP/RN1QKBNR b KQ - 2 4',         2,   63,  1721);
      SetStpr(11, 'n1n5/PPPk4/8/8/8/8/4Kppp/5N1N b - - 0 1',                              24,  496,  9483);
      SetStpr(12, '8/p7/8/1P6/K1k3p1/6P1/7P/8 w - - 0 1',                                  5,   39,   237);
      SetStpr(13, 'r3k2r/p6p/8/B7/1pp1p3/3b4/P6P/R3K2R w KQkq - 0 1',                     17,  341,  6666);
      SetStpr(14, '8/5p2/8/2k3P1/p3K3/8/1P6/8 b - - 0 1',                                  9,   85,   795);
      SetStpr(15, 'r3k2r/pb3pp1/5n1p/n2p4/1p1PPB2/6P1/P2N1PBP/R3K2R b KQkq - 0 1',        30,  986, 29777)

    end; { InitializeSelfTestSubsystem }

    procedure InitializeScoreTables;

      procedure InitializePawnAdvancementVectors;
        var
          color: colorrtype;
          bfile: bfiletype;
      begin
        for color := colorrmin to colorrmax do
          for bfile := bfilemin to bfilemax do
            begin

              { Linear advancement }

              pawnloc0[color, normalbrank[color, brank1]] := 0;
              pawnloc0[color, normalbrank[color, brank2]] := 0;
              pawnloc0[color, normalbrank[color, brank3]] := 1;
              pawnloc0[color, normalbrank[color, brank4]] := 2;
              pawnloc0[color, normalbrank[color, brank5]] := 3;
              pawnloc0[color, normalbrank[color, brank6]] := 4;
              pawnloc0[color, normalbrank[color, brank7]] := 5;
              pawnloc0[color, normalbrank[color, brank8]] := 0;

              { Cubed advancement }

              pawnloc1[color, normalbrank[color, brank1]] :=   0;
              pawnloc1[color, normalbrank[color, brank2]] :=   0;
              pawnloc1[color, normalbrank[color, brank3]] :=   1;
              pawnloc1[color, normalbrank[color, brank4]] :=   8;
              pawnloc1[color, normalbrank[color, brank5]] :=  27;
              pawnloc1[color, normalbrank[color, brank6]] :=  64;
              pawnloc1[color, normalbrank[color, brank7]] := 125;
              pawnloc1[color, normalbrank[color, brank8]] :=   0

            end
      end; { InitializePawnAdvancementVectors }

    begin
      InitializePawnAdvancementVectors
    end; { InitializeScoreTables }

    procedure InitializeStaticMoves;
    begin

      { Initialize the null move }

      MoveSynthM4(nullmove, sqa1, sqa1, manvv, mscreg);
      MoveFlagSet(nullmove, mfnull);

      { Initialize the void move }

      MoveSynthM4(voidmove, sqa1, sqa1, manvv, mscreg);
      MoveFlagSet(voidmove, mfvoid)

    end; { InitializeStaticMoves }

    procedure InitializeStartItems;
      var
        bfile: bfiletype;
        brank: branktype;
    begin

      { Initialize the constant initial array chessboard }

      with startboard do
        begin
          sqv[sqa1] := manwr;
          sqv[sqb1] := manwn;
          sqv[sqc1] := manwb;
          sqv[sqd1] := manwq;
          sqv[sqe1] := manwk;
          sqv[sqf1] := manwb;
          sqv[sqg1] := manwn;
          sqv[sqh1] := manwr;
          for bfile := bfilemin to bfilemax do
            begin
              rfv[brank2, bfile] := manwp;
              for brank := brank3 to brank6 do
                rfv[brank, bfile] := manvv;
              rfv[brank7, bfile] := manbp
            end;
           sqv[sqa8] := manbr;
           sqv[sqb8] := manbn;
           sqv[sqc8] := manbb;
           sqv[sqd8] := manbq;
           sqv[sqe8] := manbk;
           sqv[sqf8] := manbb;
           sqv[sqg8] := manbn;
           sqv[sqh8] := manbr;
        end
    end; { InitializeStartItems }

    procedure InitializeOptionStrings;
    begin

      { Initialize option names }

      optnnames[optnadcc] := 'adcc';
      optnnames[optnadcp] := 'adcp';
      optnnames[optnmono] := 'mono';
      optnnames[optntrcv] := 'trcv';
      optnnames[optntrea] := 'trea';
      optnnames[optntrfd] := 'trfd';
      optnnames[optntrfv] := 'trfv';
      optnnames[optntrif] := 'trif';
      optnnames[optntrit] := 'trit';
      optnnames[optntrpv] := 'trpv';
      optnnames[optntrst] := 'trst';
      optnnames[optntrts] := 'trts';

      { Initialize option help strings }

      optnhelps[optnadcc] := 'Auto display: chess clock';
      optnhelps[optnadcp] := 'Auto display: chess position';
      optnhelps[optnmono] := 'Monochrome only output';
      optnhelps[optntrcv] := 'Trace: current variation';
      optnhelps[optntrea] := 'Trace: EPD analysis';
      optnhelps[optntrfd] := 'Trace: first time node at depth';
      optnhelps[optntrfv] := 'Trace: final (predicted) variation';
      optnhelps[optntrif] := 'Trace: input FEN';
      optnhelps[optntrit] := 'Trace: iteration start/finish';
      optnhelps[optntrpv] := 'Trace: predicted variation';
      optnhelps[optntrst] := 'Trace: search termination';
      optnhelps[optntrts] := 'Trace: timing statistics'

    end; { InitializeOptionStrings }

    procedure InitializeCommandStrings;

      procedure InitializeIcpCommandStrings;
      begin

        { Initialize the ICP command verbs }

        icpcnames[icpcbench]     := 'bench';
        icpcnames[icpcd]         := 'd';
        icpcnames[icpcdao]       := 'dao';
        icpcnames[icpcdb]        := 'db';
        icpcnames[icpcdbbdb]     := 'dbbdb';
        icpcnames[icpcdbcolor]   := 'dbcolor';
        icpcnames[icpcdbmono]    := 'dbmono';
        icpcnames[icpcdesc]      := 'desc';
        icpcnames[icpcdfen]      := 'dfen';
        icpcnames[icpcdm]        := 'dm';
        icpcnames[icpcdmsig]     := 'dmsig';
        icpcnames[icpcdobm]      := 'dobm';
        icpcnames[icpcdp]        := 'dp';
        icpcnames[icpcdpgn]      := 'dpgn';
        icpcnames[icpcdpi]       := 'dpi';
        icpcnames[icpcdps]       := 'dps';
        icpcnames[icpcdtbm]      := 'dtbm';
        icpcnames[icpcdtbs]      := 'dtbs';
        icpcnames[icpcecho]      := 'echo';
        icpcnames[icpcefnormal]  := 'efnormal';
        icpcnames[icpcexit]      := 'exit';
        icpcnames[icpcffmate]    := 'ffmate';
        icpcnames[icpcffnormal]  := 'ffnormal';
        icpcnames[icpcffperft]   := 'ffperft';
        icpcnames[icpcg]         := 'g';
        icpcnames[icpcgg]        := 'gg';
        icpcnames[icpchelp]      := 'help';
        icpcnames[icpcloadfen]   := 'loadfen';
        icpcnames[icpcloadpgn]   := 'loadpgn';
        icpcnames[icpcmate]      := 'mate';
        icpcnames[icpcmtperft]   := 'mtperft';
        icpcnames[icpcnew]       := 'new';
        icpcnames[icpcnoop]      := 'noop';
        icpcnames[icpcoptreset]  := 'optreset';
        icpcnames[icpcoptset]    := 'optset';
        icpcnames[icpcperftbulk] := 'perftbulk';
        icpcnames[icpcperftfull] := 'perftfull';
        icpcnames[icpcperfttran] := 'perfttran';
        icpcnames[icpcpfnormal]  := 'pfnormal';
        icpcnames[icpcrg]        := 'rg';
        icpcnames[icpcrgdump]    := 'rgdump';
        icpcnames[icpcrgstat]    := 'rgstat';
        icpcnames[icpcrm]        := 'rm';
        icpcnames[icpcrmp]       := 'rmp';
        icpcnames[icpcrmts]      := 'rmts';
        icpcnames[icpcs]         := 's';
        icpcnames[icpcsavefen]   := 'savefen';
        icpcnames[icpcsavepgn]   := 'savepgn';
        icpcnames[icpcselftest]  := 'selftest';
        icpcnames[icpcsfen]      := 'sfen';
        icpcnames[icpcslevfd]    := 'slevfd';
        icpcnames[icpcslevfn]    := 'slevfn';
        icpcnames[icpcslevft]    := 'slevft';
        icpcnames[icpcslevnt]    := 'slevnt';
        icpcnames[icpcslevut]    := 'slevut';
        icpcnames[icpcstag]      := 'stag';
        icpcnames[icpctest]      := 'test';
        icpcnames[icpcttreset]   := 'ttreset';

        { Initialize the ICP command help strings }

        icpchelps[icpcbench]     := 'Run the benchmark';
        icpchelps[icpcd]         := 'Display everything';
        icpchelps[icpcdao]       := 'Display active options';
        icpchelps[icpcdb]        := 'Display board';
        icpchelps[icpcdbbdb]     := 'Display bitboard database';
        icpchelps[icpcdbcolor]   := 'Display board (ANSI color)';
        icpchelps[icpcdbmono]    := 'Display board (monochrome)';
        icpchelps[icpcdesc]      := 'Display evaluation score components';
        icpchelps[icpcdfen]      := 'Display FEN';
        icpchelps[icpcdm]        := 'Display moves';
        icpchelps[icpcdmsig]     := 'Display material signature';
        icpchelps[icpcdobm]      := 'Display opening book moves';
        icpchelps[icpcdp]        := 'Display position';
        icpchelps[icpcdpgn]      := 'Display PGN';
        icpchelps[icpcdpi]       := 'Display program identification';
        icpchelps[icpcdps]       := 'Display pawn structure components';
        icpchelps[icpcdtbm]      := 'Display tablebase moves';
        icpchelps[icpcdtbs]      := 'Display tablebase score';
        icpchelps[icpcecho]      := 'Echo parameters';
        icpchelps[icpcefnormal]  := 'Normalize from an EPD <input-file> to an EPD <output-file>';
        icpchelps[icpcexit]      := 'Exit program';
        icpchelps[icpcffmate]    := 'Scan FEN <input-file> data, find mate in <number> full moves';
        icpchelps[icpcffnormal]  := 'Normalize from a FEN <input-file> to a FEN <output-file>';
        icpchelps[icpcffperft]   := 'Summing over a FEN <input-file> data, run perft to <depth>';
        icpchelps[icpcg]         := 'Search for a move and then play it';
        icpchelps[icpcgg]        := 'Play both sides until the end of the game';
        icpchelps[icpchelp]      := 'Show help';
        icpchelps[icpcloadfen]   := 'Load FEN from an <input-file>';
        icpchelps[icpcloadpgn]   := 'Load PGN from an <input-file>';
        icpchelps[icpcmate]      := 'Search for a checkmate in <number> full moves';
        icpchelps[icpcmtperft]   := 'Run multithreaded perft to <depth> with full node visits';
        icpchelps[icpcnew]       := 'New game';
        icpchelps[icpcnoop]      := 'No operation';
        icpchelps[icpcoptreset]  := 'Reset <option> [<option>]*';
        icpchelps[icpcoptset]    := 'Set <option> [<option>]*';
        icpchelps[icpcperftbulk] := 'Run perft to <depth> with bulk counting';
        icpchelps[icpcperftfull] := 'Run perft to <depth> with each node visited';
        icpchelps[icpcperfttran] := 'Run perft to <depth> with transposition help';
        icpchelps[icpcpfnormal]  := 'Normalize from a PGN <input-file> to a PGN <output-file>';
        icpchelps[icpcrg]        := 'Generate and display a single random game';
        icpchelps[icpcrgdump]    := 'Dump to a PGN <output-file> <number> random games';
        icpchelps[icpcrgstat]    := 'Generate a report for <number> random game(s)';
        icpchelps[icpcrm]        := 'Retract move';
        icpchelps[icpcrmp]       := 'Retract move pair';
        icpchelps[icpcrmts]      := 'Retract move(s) to start';
        icpchelps[icpcs]         := 'Search for a move but do not play it';
        icpchelps[icpcsavefen]   := 'Save FEN to an <output-file>';
        icpchelps[icpcsavepgn]   := 'Save PGN to an <output-file>';
        icpchelps[icpcselftest]  := 'Run the self test';
        icpchelps[icpcsfen]      := 'Set FEN <mpd> <good> <cavs> <epsq> <hmvc> <fmvn>';
        icpchelps[icpcslevfd]    := 'Set level fixed depth <ply>';
        icpchelps[icpcslevfn]    := 'Set level fixed nodes <count>';
        icpchelps[icpcslevft]    := 'Set level fixed time <seconds>';
        icpchelps[icpcslevnt]    := 'Set level nominal time <seconds>';
        icpchelps[icpcslevut]    := 'Set level unlimited time';
        icpchelps[icpcstag]      := 'Set PGN <tagname> to <tagvalue>';
        icpchelps[icpctest]      := 'Run developer test';
        icpchelps[icpcttreset]   := 'Transposition table data reset'

      end; { InitializeIcpCommandStrings }

      procedure InitializeScpCommandStrings;
      begin
        {TBD}
      end; { InitializeScpCommandStrings }

    begin
      InitializeIcpCommandStrings;
      InitializeScpCommandStrings
    end; { InitializeCommandStrings }

  begin
    InitializePrngSubsystem;
    InitializeBasicSubsystem;
    InitializeDirectionalTables;
    InitializeSquareScanningSubsystem;
    InitializeBitboardSubsystem;
    InitializeAttackCounts;
    InitializeHashSubsystem;
    InitializeCastlingSubsystem;
    InitializeEpdSubsystem;
    InitializePgnSubsystem;
    InitializeTablebaseSubsystem;
    InitializeSelfTestSubsystem;
    InitializeStaticMoves;
    InitializeScoreTables;
    InitializeStartItems;
    InitializeOptionStrings;
    InitializeCommandStrings;
    Randomize;
    Assert(SelfTest(Output), 'Initialize: Self test fault')
  end; { Initialize }

  procedure Terminate;
  begin
  end; { Terminate }

{ ***** Command processor drivers ***** }

  procedure DriveIcp;
    var
      icpptr: ^icptype;
  begin

    { Sign on }

    WriteStrNL(Output, progcopy);

    { Allocate and initialize the command processor }

    New(icpptr);
    IcpInit(icpptr^);

    { Report ready }

    WriteStrNL(Output, progname + ' ready');
    WriteNL(Output);

    { Process the interactive command stream }

    IcpCycle(icpptr^);

    { Terminate and deallocate the command processor }

    IcpTerm(icpptr^);
    Dispose(icpptr);

    { Sign off }

    WriteNL(Output);
    WriteStrNL(Output, progname + ' done')

  end; { DriveIcp }

  procedure DriveScp;
    var
      scpptr: ^scptype;
  begin
    New(scpptr);
    ScpInit(scpptr^);
    {TBD}
    ScpTerm(scpptr^);
    Dispose(scpptr)
  end; { DriveScp }

{ ***** Main program ***** }

begin
  Initialize;
  DriveIcp;
  Terminate
end. { CookieCat (Meow!) }
