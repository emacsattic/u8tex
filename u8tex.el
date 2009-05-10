;;; quail/u8tex.el -- Quail package to input in -*- coding: utf-8 -*-

;; Copyright (C) 2000 Sergei Pokrovsky
;; Time-stamp: <2000-12-08 19:00:30 pok>,  v. 1.2

;; Keywords: mule, multilingual, unicode, input method, TeX

;; Based on definitions stolen from "unicode-input.el" by
;; Florian Weimer <fw@s.netic.de>.

;; The latest version is to be found at CTAN/support/emacs-modes/u8tex.el;
;; e.g. <ftp://ftp.dante.de/tex-archive/support/emacs-modes/u8tex.el>.

;; This file is not a part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:
;;
;; This file is intended for use with Markus Kuhn's Unicode fonts,
;; see <http://www.cl.cam.ac.uk/~mgk25/unicode.html>, and the
;; Otfried Cheong's extension of Mule-UCS, available at
;; <http://www.cs.uu.nl/~otfried/Mule/>.

;; The idea is to provide a routine way to input the many TeX
;; characters (and some more) using the familiar TeX notation.  Surely
;; it is not convenient for typing a French or German text, for which
;; there are special packages; but I prefer to use it for a mixed
;; text, where some accented characters from various languages occur
;; sporadically, and it is better to type a longer key sequence
;; /"Arger for Ärger rather than suffer from unexpected äny" when
;; typing "any" (as it is usual with the shorter `"Arger' manner, or
;; with o'clock becoming oćlock etc).

;; I've taken some liberties with the TeX notation:
;; 1. Backslash is replaced with solidus in its escape function.  The
;;    reason is obvious: TeX users heavily use backspace for many other
;;    purposes as well.
;; 2. The prefix "text" is systematically dropped; just /euro rather
;;    than /texteuro, /perthousand rather than \textperthousand.
;; 3. No internal spaces, e.g. /cC rather than {/c C} or /c{C}.
;; 4. /! and /? are used instead of !` and ?` -- like in EuroTeX,
;;    just to reduce the number of escape characters.
;; 5. /3/4 etc is used instead of \textthreequarters.
;; 6. If HTML offers a ahorter Latin-1 name, it is preferred:
;;    /reg rather than \textregistered, /nbsp rather than \nobreakspace,
;;    /copy rather than \copyright etc. (Such abbreviations are marked
;;    with "HTML" in a comment field.)

;; Installation:

;; Save this file as quail/u8tex.el (the "quail" may be your
;; emacs/20.*/leim/quail or a directory on your load-path), byte
;; compile it and put a record like this:
;; 
;; (register-input-method
;;  "u8tex" "utf-8" 'quail-use-package
;;  "τεχ" "Unicode input using (Euro)TeX names"
;;  "quail/u8tex")
;;
;; into emacs/20.*/leim/leim-list.el (probably there exists a more
;; civilized way to extend leim-list?).  Then (after reloading Mule)
;; you can switch to u8tex in the usual way (`C-x C-m C-\ u8tex'; the
;; first u... is sufficient for completion in my environment).

;;; Changes in v. 1.2:
;; 1. Documentation (reference to Otfried's package).
;; 2. Some HTML abbreviations are adopted (/copy, /reg etc).
;; 3. Errors corrected: /permil
;; 4. More amssymb characters.

;;; Code:

(require 'quail)

(quail-define-package
 "u8tex" "utf-8" "τεχ" t
 "Input Unicode characters using (Euro)TeX names.
Use solidus (/) instead of backslash as Mule escape.

    effect   | prefix | examples
 ------------+--------+-------------------
    acute    |   /'   | /'a → á   /'{} → ́
    grave    |   /`   | /`a → à   /`{} → ̀
  circumflex |   /^   | /^a → â   /^{} → ̂
   diæresis  |   /\"   | /\"a → ä   /\"{} → ̈
  dot above  |   /.   | /.z → ż   /.I → İ
   macron    |   /=   | /=a → ā   /=e → ē   /=H → Ħ
 breve, háček| /u  /v | /ua → ă   /vc → č
   cedilla   |   /c   | /cc → ç   /cs → ş
   ogonek    |   /k   | /ka → ą   /kE → Ę

// → /; /lq → ‘; /glqq → „; /S → §; /AE → Æ; /DH → Ð;  x^2 → x²; /div → ÷  etc.

" nil t nil nil nil nil nil nil nil nil t)

(quail-define-rules

 ("/`A" ?À) ("/`a" ?à)
 ("/`E" ?È) ("/`e" ?è)
 ("/`I" ?Ì) ("/`i" ?ì)
 ("/`O" ?Ò) ("/`o" ?ò)
 ("/`U" ?Ù) ("/`u" ?ù)

 ("/'A" ?Á) ("/'a" ?á)
 ("/'C" ?Ć) ("/'c" ?ć)
 ("/'E" ?É) ("/'e" ?é)
 ("/'I" ?Í) ("/'i" ?í)
 ("/'N" ?Ń) ("/'n" ?ń)
 ("/'L" ?Ĺ) ("/'l" ?ĺ)
 ("/'O" ?Ó) ("/'o" ?ó)
 ("/'R" ?Ŕ) ("/'r" ?ŕ)
 ("/'S" ?Ś) ("/'s" ?ś)
 ("/'U" ?Ú) ("/'u" ?ú)
 ("/'Y" ?Ý) ("/'y" ?ý)
 ("/'Z" ?Ź) ("/'z" ?ź)

 ("/^A" ?Â) ("/^a" ?â)
 ("/^C" ?Ĉ) ("/^c" ?ĉ)
 ("/^E" ?Ê) ("/^e" ?ê)
 ("/^G" ?Ĝ) ("/^g" ?ĝ)
 ("/^H" ?Ĥ) ("/^h" ?ĥ)
 ("/^I" ?Î) ("/^i" ?î)
 ("/^J" ?Ĵ) ("/^j" ?ĵ)
 ("/^O" ?Ô) ("/^o" ?ô)
 ("/^S" ?Ŝ) ("/^s" ?ŝ)
 ("/^U" ?Û) ("/^u" ?û)
 ("/^W" ?Ŵ) ("/^w" ?ŵ)
 ("/^Y" ?Ŷ) ("/^y" ?ŷ)

 ("/~A" ?Ã) ("/~a" ?ã)
 ("/~I" ?Ĩ) ("/~i" ?ĩ)
 ("/~N" ?Ñ) ("/~n" ?ñ)
 ("/~I" ?Ĩ) ("/~i" ?ĩ)
 ("/~O" ?Õ) ("/~o" ?õ)
 ("/~U" ?Ũ) ("/~u" ?ũ)

 ("/rU" ?Ů) ("/ru" ?ů) ; \r[ing] like en EuroTeX

 ("/\"A" ?Ä) ("/\"a" ?ä)
 ("/\"E" ?Ë) ("/\"e" ?ë)
 ("/\"I" ?Ï) ("/\"i" ?ï)
 ("/\"O" ?Ö) ("/\"o" ?ö)
 ("/\"U" ?Ü) ("/\"u" ?ü)
 ("/\"Y" ?Ÿ) ("/\"y" ?ÿ)

 ("/cC" ?Ç) ("/cc" ?ç)
 ("/cG" ?Ģ) ("/cg" ?ģ) ; actually it must be comma
 ("/cN" ?Ņ) ("/cn" ?ņ)
 ("/cS" ?Ş) ("/cs" ?ş)
 ("/cT" ?Ţ) ("/ct" ?ţ) ; actually it must be comma

 ("/=A" ?Ā) ("/=a" ?ā)
 ("/=E" ?Ē) ("/=e" ?ē)
 ("/=I" ?Ī) ("/=i" ?ī)
 ("/=O" ?Ō) ("/=o" ?ō)
 ("/=U" ?Ū) ("/=u" ?ū)
 ("/=H" ?Ħ) ("/=h" ?ħ) ; abuse
 ("/=T" ?Ŧ) ("/=t" ?ŧ) ; abuse

 ("/uA" ?Ă) ("/ua" ?ă)
 ("/uE" ?Ĕ) ("/ue" ?ĕ)
 ("/uG" ?Ğ) ("/ug" ?ğ)
 ("/uI" ?Ĭ) ("/ui" ?ĭ)
 ("/uO" ?Ŏ) ("/uo" ?ŏ)
 ("/uU" ?Ŭ) ("/uu" ?ŭ)

 ("/vC" ?Č) ("/vc" ?č)
 ("/vD" ?Ď) ("/vd" ?ď)
 ("/vE" ?Ě) ("/ve" ?ě)
 ("/vL" ?Ľ) ("/vl" ?ľ)
 ("/vN" ?Ň) ("/vn" ?ň)
 ("/vR" ?Ř) ("/vr" ?ř)
 ("/vS" ?Š) ("/vs" ?š)
 ("/vT" ?Ť) ("/vt" ?ť)
 ("/vZ" ?Ž) ("/vz" ?ž)

 ("/.A" ?Ȧ) ("/.a" ?ȧ)
 ("/.C" ?Ċ) ("/.c" ?ċ)
 ("/.E" ?Ė) ("/.e" ?ė)
 ("/.G" ?Ġ) ("/.g" ?ġ)
 ("/.I" ?İ) ("/i"  ?ı) ; also \imath
 ("/.O" ?Ȯ) ("/.o" ?ȯ)
 ("/.Z" ?Ż) ("/.z" ?ż)

 ("/HO" ?Ő) ("/Ho" ?ő)
 ("/HU" ?Ű) ("/Hu" ?ű)

 ("/kA" ?Ą) ("/ka" ?ą)
 ("/kE" ?Ę) ("/ke" ?ę)
 ("/kI" ?Į) ("/ki" ?į)
 ("/kU" ?Ų) ("/ku" ?ų)

 ("/AA" ?Å) ("/aa" ?å)
 ("/AE" ?Æ) ("/ae" ?æ)
 ("/DH" ?Ð) ("/dh" ?ð)
 ("/DJ" ?Đ) ("/dj" ?đ)
 ("/Y" ?Ĳ) ("/y" ?ĳ) ; Dutch ij
 ("/L" ?Ł) ("/l" ?ł)
 ("/Lp" ?Ŀ) ("/lp" ?ŀ) ; Catalan l dot, as in paraŀlel
 ("/NG" ?Ŋ) ("/ng" ?ŋ)
 ("/O" ?Ø) ("/o" ?ø)
 ("/OE" ?Œ) ("/oe" ?œ)
 ("/longs"  ?ſ)
 ("/ss" ?ß)
 ("/st" ?ﬅ) ; or ?ﬆ
 ("/TH" ?Þ) ("/th" ?þ)

 ;; Lowercase Greek letters
 ;; (the missing caps like \Alpha come first)

 ("/Alpha" ?Α) ("/alpha" ?α)
 ("/Beta" ?Β) ("/beta" ?β)
 ("/gamma" ?γ) ("/Gamma" ?Γ)
 ("/delta" ?δ) ("/Delta" ?Δ)
 ("/Epsilon" ?Ε) ("/epsilon" ?ε)
 ("/Zeta" ?Ζ) ("/zeta" ?ζ)
 ("/Eta" ?Η) ("/eta" ?η)
 ("/theta" ?θ) ("/vartheta" ?ϑ) ("/Theta" ?Θ)
 ("/Iota" ?Ι) ("/iota" ?ι)
 ("/Kappa" ?Κ) ("/kappa" ?κ)
 ("/lambda" ?λ) ("/Lambda" ?Λ)
 ("/Mu" ?Μ) ("/mu" ?μ)
 ("/Nu" ?Ν) ("/nu" ?ν)
 ("/Omicron" ?Ο) ("/omicron" ?ο)
 ("/xi" ?ξ) ("/Xi" ?Ξ)
 ("/pi" ?π) ("/varpi" ?ϖ) ("/Pi" ?Π)
 ("/Rho" ?Ρ) ("/rho" ?ρ) ("/varrho" ?ϱ)
 ("/sigma" ?σ) ("/varsigma" ?ς) ("/Sigma" ?Σ)
 ("/Tau" ?Τ) ("/tau" ?τ)
 ("/upsilon" ?υ) ("/Upsilon" ?Υ)
 ("/phi" ?ϕ) ("/varphi" ?φ) ("/Phi" ?Φ)
 ("/Chi" ?Χ) ("/chi" ?χ)
 ("/psi" ?ψ) ("/Psi" ?Ψ)
 ("/omega" ?ω) ("/Omega" ?Ω)

 ;; Miscellaneous symbols

 ("/aleph" ?ℵ) ("/beth" ?ℶ) ("/gimel" ?ℷ) ("/daleth" ?ℸ)
 ("/hbar" ?ℏ)
 ("/imath" ?ı)
 ("/ell" ?ℓ)
 ("/wp" ?℘)
 ("/Re" ?ℜ) ("/Im" ?ℑ)
 ("/partial" ?∂)
 ("/infty" ?∞)
 ("/prime" ?′)
 ("/emptyset" ?∅)
 ("/nabla" ?∇)
 ("/surd" ?√)
 ("/top" ?⊤)
 ("/bot" ?⊥)
 ("/|" ?∥)
 ("/angle" ?∠)
 ("/triangle" ?△)
 ("/backslash" ?\\)
 ("//" ?/) ; special !!
 ("/forall" ?∀) ("/exists" ?∃)
 ("/neg" ?¬)
 ("/flat" ?♭) ("/natural" ?♮) ("/sharp" ?♯)
 ("/clubsuit" ?♣) ("/diamondsuit" ?♢)
 ("/heartsuit" ?♡) ("/spadesuit" ?♠)
 ("/mho" ?℧) ("/complement" ?∁) ("/lozenge" ?◊) ; amssymb
 ("/square" ?□) ("/blacksquare" ?■) ; amssymb
 ("/barwedge" ?⊼) ("/veebar" ?⊻) ; amssymb

 ;; “Large” operators

 ("/sum" ?∑)
 ("/prod" ?∏)
 ("/coprod" ?∐)
 ("/int" ?∫)
 ("/oint" ?∮)
 ("/bigcap" ?⋂)
 ("/bigcup" ?⋃)
 ("/bigvee" ?⋁)
 ("/bigwedge" ?⋀)

 ;; Binary operations

 ("/pm" ?±) ("/mp" ?∓)
 ("/setminus" ?∖)
 ("/cdot" ?⋅) ("/times" ?×)
 ("/ast" ?∗) ("/star" ?⋆)
 ("/diamond" ?⋄)
 ("/circ" ?∘)
 ("/bullet" ?∙)
 ("/div" ?÷)
 ("/cap" ?∩) ("/cup" ?∪)
 ("/uplus" ?⊎)
 ("/sqcap" ?⊓) ("/sqcup" ?⊔)
 ("/triangleleft" ?◁)
 ("/triangleright" ?▷)
 ("/wr" ?≀)
 ("/bigcirc" ?◯)
 ("/bigtriangleup" ?△) ("/bigtriangledown" ?▽)
 ("/vee" ?∨) ("/wedge" ?∧)
 ("/oplus" ?⊕) ("/ominus" ?⊖)
 ("/otimes" ?⊗) ("/oslash" ?⊘)
 ("/odot" ?⊙)
 ("/dagger" ?†) ("/ddagger" ?‡)
 ("/amalg" ?∐)

 ;; Relations

 ("/leq" ?≤)
 ("/prec" ?≺) ("/preceq" ?≼)
 ("/ll" ?≪)
 ("/subset" ?⊂) ("/subseteq" ?⊆)
 ("/sqsubseteq" ?⊑)
 ("/in" ?∈)
 ("/vdash" ?⊢)
 ("/smile" ?⌣)
 ("/frown" ?⌢)
 ("/geq" ?≥)
 ("/succ" ?≻) ("/succeq" ?≽)
 ("/gg" ?≫)
 ("/supset" ?⊃) ("/supseteq" ?⊇)
 ("/sqsupseteq" ?⊒)
 ("/ni" ?∋)
 ("/dashv" ?⊣)
 ("/mid" ?∣)
 ("/parallel" ?∥)
 ("/equiv" ?≡)
 ("/sim" ?∼) ("/simeq" ?≃)
 ("/asymp" ?≍)
 ("/approx" ?≈)
 ("/cong" ?≅)
 ("/bowtie" ?⋈)
 ("/propto" ?∝)
 ("/models" ?⊨)
 ("/doteq" ?≐)
 ("/perp" ?⊥)

 ;; Negated relations

 ("/not<" ?≮)
 ("/not/leq" ?≰)
 ("/not/prec" ?⊀) ("/not/preceq" ?⋠)
 ("/not/subset" ?⊄) ("/not/subseteq" ?⊈)
 ("/not/sqsubseteq" ?⋢)
 ("/not>" ?≯)
 ("/not/geq" ?≱)
 ("/not/succ" ?⊁) ("/not/succeq" ?⋡)
 ("/not/supset" ?⊅) ("/not/supseteq" ?⊉)
 ("/not/sqsupseteq" ?⋣)
 ("/not=" ?≠)
 ("/not/equiv" ?≢)
 ("/not/sim" ?≁) ("/not/simeq" ?≄)
 ("/not/approx" ?≉)
 ("/not/cong" ?≇)
 ("/not/asymp" ?≭)

 ;; Arrows

 ("/leftarrow" ?←) ("/Leftarrow" ?⇐)
 ("/rightarrow" ?→) ("/Rightarrow" ?⇒)
 ("/leftrightarrow" ?↔) ("/Leftrightarrow" ?⇔)
 ("/mapsto" ?↦)
 ("/hookleftarrow" ?↩)
 ("/leftharpoonup" ?↼)
 ("/leftharpoondown" ?↽)
 ("/rightleftharpoons" ?⇌)
 ("/hookrightarrow" ?↪)
 ("/rightharpoonup" ?⇀)
 ("/rightharpoondown" ?⇁)
 ("/searrow" ?↘)
 ("/swarrow" ?↙)
 ("/nwarrow" ?↖)
 ("/uparrow" ?↑) ("/Uparrow" ?⇑)
 ("/downarrow" ?↓) ("/Downarrow" ?⇓)
 ("/updownarrow" ?↕) ("/Updownarrow" ?⇕)
 ("/nearrow" ?↗)

 ;; Openings       ;; Closings    
                                  
 ("/lfloor" ?⌊)   ("/rfloor" ?⌋)
 ("/langle" ?〈)   ("/rangle" ?〉)
 ("/lceil"  ?⌈)   ("/rceil"  ?⌉) 

 ;; Alternate names

 ("/ne" ?≠) ("/neq" ?≠)
 ("/le" ?≤) ("/ge" ?≥)
 ("/to" ?→)
 ("/gets" ?←)
 ("/owns" ?∋)
 ("/land" ?∧)
 ("/lor" ?∨)
 ("/lnot" ?¬)
 ("/vert" ?∣)
 ("/Vert" ?∥)

 ;; Non-math symbols

 ("/S" ?§) ("/P" ?¶)
 ("/dag" ?†) ("/ddag" ?‡)
 ("/brokenbar" ?¦)
 ("/brvbar" ?¦) ; like in HTML
 ("/reg" ?®)    ; like in HTML, unlike TeX's /registered
 ("/trade" ?™)  ; like in HTML
 ("/frownie" ?☹)
 ("/smiley" ?☺)
 ("/blacksmiley" ?☻)

 ;; Typographic symbols and ligatures

 ("''" ?”) ("``" ?“)
 ("/lq" ?‘) ("/rq" ?’)
 ("/flqq" ?«) ("/frqq" ?»)      ; French double quotes
 ("/flq" ?‹)  ("/frq" ?›)       ; French double quotes
 ("/glqq" ?„) ("/grqq" ?‟)      ; German double quotes
 ("/glq" ?‚)  ("/grq" ?‛)       ; German single quotes
 ("/dots" ?…)
 ("/-" ?‐)     ; 2010 (HYPHEN)
 ("/--" ?–)    ; 2013 (EN DASH)
 ("/---" ?—)   ; 2014 (EM DASH)
 ("/minus" ?−) ; 2212 (MINUS SIGN)
 ("/nbsp" ? )  ; A0 (NO-BREAK SPACE), like in HTML
; ("/thinspace" ? )
; ("/," ? )
 ("/ff" ?ﬀ)
 ("/fi" ?ﬁ)
 ("/fl" ?ﬂ)
 ("/ffi" ?ﬃ)
 ("/ffl" ?ﬄ)
 ("/!" ?¡) ("/?" ?¿); as in EuroTeX
 ("/copy" ?©)       ; like in HTML, unlike TeX's \copyright
 ("/permil" ?‰)     ; HTML (= PER MILLE SIGN) and wasysym
 ("/perthousand" ?‰); \textperthousand
 ("/micro" ?µ)      ; different from GREEK SMALL LETTER /mu
 ("/deg" ?°)        ; like in HTML, unlike TeX's \textdegree
 ("/1/4" ?¼)        ; \textonequarter
 ("/1/2" ?½)        ; \textonehalf
 ("/3/4" ?¾)        ; \textthreequarters

 ;; Combining characters

 ("/'{}" ?́)
 ("/`{}" ?̀)
 ("/^{}" ?̂)
 ("/\"{}" ?̈)
 ("/~{}" ?̃)
 ("/={}" ?¯) ; or else COMBINING MACRON = ("/={}" ?̄) ?
 ("/.{}" ?̇)
 ("/u{}" ?̆)
 ("/v{}" ?̌)
 ("/H{}" ?̋)
 ("/t{}" ?͡)
 ("/c{}" ?̧)
 ("/d{}" ?̣)
 ("/b{}" ?̱)

 ;; Subscripts

 ("_0" ?₀) ("_1" ?₁) ("_2" ?₂) ("_3" ?₃) ("_4" ?₄)
 ("_5" ?₅) ("_6" ?₆) ("_7" ?₇) ("_8" ?₈) ("_9" ?₉)
 ("_+" ?₊) ("_-" ?₋) ("_=" ?₌)
 ("_(" ?₍) ("_)" ?₎)


 ;; Superscripts

 ("^0" ?⁰) ("^1" ?¹) ("^2" ?²) ("^3" ?³) ("^4" ?⁴)
 ("^5" ?⁵) ("^6" ?⁶) ("^7" ?⁷) ("^8" ?⁸) ("^9" ?⁹)
 ("^+" ?⁺) ("^-" ?⁻) ("^=" ?⁼)
 ("^(" ?⁽) ("^)" ?⁾)
 ("^a" ?ª) ("^n" ?ⁿ) ("^o" ?º)

 ;; Currency signs

 ("/cent" ?¢)     ; after HTML and wasy
 ("/pound" ?£)    ; after HTML
 ("/curren" ?¤)   ; like in HTML, cf \textcurrency
 ("/euro" ?€)     ; \texteuro
 ("/yen" ?¥)      ; \textyen

 ;; \mathbb

 ("/bbC" ?ℂ) ("/bbH" ?ℍ) ("/bbN" ?ℕ) ("/bbP" ?ℙ)
 ("/bbQ" ?ℚ) ("/bbR" ?ℝ) ("/bbZ" ?ℤ)

;; IPA (there is a dedicated MULE method!)

 ("/turna" ?ɐ)
 ("/scripta" ?ɑ)
 ("/turnscripta" ?ɒ)
 ("/turnv" ?ʌ)
 ("/dezh" ?ʤ)
 ("/schwa" ?ə) ("/inve" ?ə)
 ("/schwahook" ?ɚ)
 ("/scriptg" ?ɡ)
 ("/turnh" ?ɥ)
 ("/openo" ?ɔ)
 ("/scr" ?ʀ)
 ("/invscr" ?ʁ)
 ("/tesh" ?ʧ)
 ("/upsilon" ?ʊ)
 ("/turnw" ?ʍ)
 ("/turny" ?ʎ)
 ("/esh" ?ʃ)
 ("/ezh" ?ʒ)
 ("/long" ?ː)
 ("/stress" ?ˈ) ; primary stress
 ("/secstress" ?ˌ) ; secondary stress

; Ancient Cyrillic (after x2enc):

 ("/FITA"   ?Ѳ) ("/fita"   ?ѳ)
 ("/YAT"    ?Ѣ) ("/yat"    ?ѣ) 
 ("/BYUS"   ?Ѫ) ("/byus"   ?ѫ)
 ("/LYUS"   ?Ѧ) ("/lyus"   ?ѧ)
 ("/CYREPS" ?Є) ("/cyreps" ?є)
 ("/IE"     ?Ѥ) ("/ie"     ?ѥ)
 ("/`I"     ?Ѝ) ("/`i"     ?ѝ)
 ("/OT"     ?Ѿ) ("/ot"     ?ѿ)
 ("/UK"     ?Ѹ) ("/uk"     ?ѹ)
 ("/IZH"    ?Ѵ) ("/izh"    ?ѵ)
 ("/\"IZH"  ?Ѷ) ("/\"izh"  ?ѷ)
 
)

;;; u8tex.el ends here
