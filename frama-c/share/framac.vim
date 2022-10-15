" Vim syntax file
" Language:     Frama-C annotations in C programs 
" Maintainers:  Anne Pacalet (anne.pacalet@inria.fr)
"
" Last Change: 
"              - 2009 Jul 01 - first very basic version included in c syntax
"              - 2010 Dec 09 - separate syntax file for Frama-C
"
" You can put this file in your .vim/syntax, and you have to modify (or create)
" .vim/after/syntax/c.vim and copy these lines :
"
" syn include @FC syntax/framac.vim
" syn region framacComment1 matchgroup=framacComment start="/\*@"rs=e-1 end="\*/ contains=@FC
" syn region framacComment2 matchgroup=framacComment start="//@"rs=e-1 end="\n" contains=@FC
"
" so you use the normal C syntax highlighting, 
" and enhance it with Frama-C annotations highlighting.
"-------------------------------------------------------------------------------

syn match framacStart /@/ 

syn region framacCommentInComment start="//" end="\n" containedin=framacComment1 contained
syn region framacCommentInComment excludenl start="//" end="$" containedin=framacComment2 contained

"-------------------------------------------------------------------------------

syn match framacKeyword /complete behaviors/ 
syn match framacKeyword /disjoint behaviors/ 
syn keyword framacKeyword behavior 
syn keyword framacKeyword assumes 
syn keyword framacKeyword requires 
syn keyword framacKeyword ensures 
syn keyword framacKeyword exits 
syn keyword framacKeyword returns 
syn keyword framacKeyword continues 
syn keyword framacKeyword breaks 
syn keyword framacKeyword requires 
syn keyword framacKeyword assert 
syn keyword framacKeyword assigns 
syn keyword framacKeyword invariant 
syn keyword framacKeyword decreases 
syn keyword framacKeyword terminates 
syn match framacKeyword /global invariant/ 
syn match framacKeyword /loop invariant/ 
syn match framacKeyword /loop variant/ 
syn match framacKeyword /loop assigns/ 
syn match framacKeyword /logic type/ 
syn keyword framacKeyword predicate 
syn keyword framacKeyword logic 
syn keyword framacKeyword ghost 
syn keyword framacKeyword axiom 
syn keyword framacKeyword lemma 
syn keyword framacKeyword axiomatic 
syn keyword framacKeyword reads 

syn match framacKeyword2 /\\true/ 
syn match framacKeyword2 /\\false/ 
syn match framacKeyword2 /\\nothing/ 
syn match framacKeyword2 /\\result/ 
syn match framacKeyword2 /\\from/ 
syn match framacKeyword2 /\\exit_status/ 
syn match framacKeyword2 /\\old/ 
syn match framacKeyword2 /\\at/ 
syn match framacKeyword2 /\\forall/ 
syn keyword framacKeyword2 /Here/ 
syn keyword framacKeyword2 /Pre/ 
syn keyword framacKeyword2 /Post/ 
syn keyword framacKeyword2 /Old/ 

"-------------------------------------------------------------------------------

syn match framacEqError "[^=!<>]=[^=]" 

"-------------------------------------------------------------------------------

hi framacStart guibg=bg guifg=Orange gui=bold

hi link framacEqError framacError
hi link framacError Error

hi link framacCommentInComment Comment

hi link framacComment1 framacComment
hi link framacComment2 framacComment
hi framacComment  guibg=#fff2db guifg=DimGrey
hi framacKeyword guibg=#fff2db guifg=Orange gui=underline

hi framacKeyword2 guibg=#fff2db guifg=#00b333 gui=bold

"-------------------------------------------------------------------------------
