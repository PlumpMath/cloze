# cloze

Experimental library for rewritable data templates. More to come if experiments bear fruit.

## Goals and questions

- Implement lambda-calculus-like system with associative interface.
- Explore potential of rewrite systems without pattern matching.

The plan is to provide a fully extensible, context-sensitive replacement protocol for elements that can manipulate and examine their context within a data structure, enabling otherwise difficult or impossible behavior such as splicing to be defined ala carte. This can be achieved by passing the zipper itself (as a reification of the current position within the data structure) to the replacement method of certain elements.

```clojure
(->
  (clozeur '#{a} '[:start a :end])
  (bind 'a (splicing [0 1 2 3]))
  collapse)

;=> [:start 0 1 2 3 :end]
```


## License

Copyright © 2015 Tims Gardner

Distributed under the Eclipse Public License either version 1.0 or (at
your option) any later version.
