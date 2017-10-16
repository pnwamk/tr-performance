#lang typed/racket/base

(provide
 Board
 Tile
 tile?
 tile<=?
 tile->string
 ALL-TILES
 STARTER-TILES#
 FOUNDING GROWING MERGING SINGLETON IMPOSSIBLE
 *create-board-with-hotels
 affordable?
 board-tiles
 board?
 deduplicate/hotel
 distinct-and-properly-formed
 found-hotel
 free-spot?
 grow-hotel
 growing-which
 make-board
 merge-hotels
 merging-which
 place-tile
 set-board
 size-of-hotel
 what-kind-of-spot
 )

;; -----------------------------------------------------------------------------

(require
 "types.rkt")

(define-type Board (HashTable Tile Content))
(define-type Tile tile)
(define board? hash?)
(require "board.rkt")
