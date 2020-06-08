FROM coqorg/coq

RUN sudo apt-get update && sudo apt-get -y upgrade && sudo apt-get -y install emacs wget
RUN wget http://adam.chlipala.net/cpdt/cpdt.tgz && tar xzfv cpdt.tgz

RUN ["/bin/bash", "-c", "source /home/coq/.profile && cd /home/coq/cpdt && make"]

COPY emacs /home/coq/.emacs

RUN sudo chown coq.coq /home/coq/.emacs
RUN echo 'test -r /home/coq/.opam/opam-init/init.sh && . /home/coq/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true' >> /home/coq/.bashrc

ENTRYPOINT ["/bin/bash"]
