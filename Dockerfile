FROM coqorg/coq:8.18-native
ADD --chown=1000:1000 . /proofs/
WORKDIR /proofs
RUN make
RUN make coqdoc
