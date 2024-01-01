FROM coqorg/coq:8.15-native
ADD --chown=1000:1000 . /proofs/
WORKDIR /proofs
RUN make
RUN make coqdoc
