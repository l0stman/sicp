(define (require p)
  (if (not p) (amb)))

(define nouns '(noun student professor cat class))
(define verbs '(verb studies lectures eats sleeps is))
(define articles '(article the a))
(define prepositions '(prep for to in by with))
(define adjectives '(adj good bad ugly interesting smart dumb))
(define adverbs '(adv quickly greatly lovely naturally))

(define (parse-attributive-adj-phrase)
  (list 'attributive-adj-phrase
        (parse-word articles)
        (parse-word adjectives)
        (parse-word nouns)))

(define (parse-prepositional-phrase)
  (list 'prep-phrase
        (parse-word prepositions)
        (parse-noun-phrase)))

(define (parse-sentence)
  (let ((noun (parse-noun-phrase))
        (verb (parse-verb-phrase)))
    (amb
     (list 'sentence noun verb)
     (list 'sentence
           (amb
            (list 'predicative-adj-phrase
                  noun
                  verb
                  (parse-word adjectives))
            (list 'adverb-phrase
                  noun
                  verb
                  (parse-word adverbs)))))))

(define (parse-verb-phrase)
  (define (maybe-extend verb-phrase)
    (amb verb-phrase
         (maybe-extend (list 'verb-phrase
                             verb-phrase
                             (parse-prepositional-phrase)))))
  (maybe-extend (parse-word verbs)))

(define (parse-simple-noun-phrase)
  (list 'simple-noun-phrase
        (parse-word articles)
        (parse-word nouns)))
(define (parse-noun-phrase)
  (define (maybe-extend noun-phrase)
    (amb noun-phrase
         (maybe-extend (list 'noun-phrase
                             noun-phrase
                             (parse-prepositional-phrase)))))
  (maybe-extend
   (amb (parse-simple-noun-phrase)
        (parse-attributive-adj-phrase))))

(define (parse-word word-list)
  (require (not (null? *unparsed*)))
  (require (memq (car *unparsed*) (cdr word-list)))
  (let ((found-word (car *unparsed*)))
    (set! *unparsed* (cdr *unparsed*))
    (list (car word-list) found-word)))

(define *unparsed* '())
(define (parse input)
  (set! *unparsed* input)
  (let ((sent (parse-sentence)))
    (require (null? *unparsed*))
    sent))
