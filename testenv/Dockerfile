FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && \
    apt-get -y upgrade && \
    apt-get install -y build-essential && \
    apt-get install -y software-properties-common && \
    apt-get install -y curl git man unzip vim wget && \
    apt-get install -y clang-14 && \
    rm -rf /var/lib/apt/lists/*

RUN curl https://sh.rustup.rs -sSf | bash -s -- -y

ENV PATH="/root/.cargo/bin:${PATH}"
RUN rustup install 1.64.0 && \
    rustup default 1.64.0


ENV HOME /root
WORKDIR /root

# Csmith
RUN wget https://github.com/csmith-project/csmith/archive/refs/tags/csmith-2.3.0.tar.gz && \
    tar -xzf csmith-2.3.0.tar.gz && \
    cd csmith-csmith-2.3.0 && \
    apt-get update && \
    apt-get -y install g++ cmake m4
RUN cd csmith-csmith-2.3.0 && \
    cmake . && \
    make && \
    make install && \
    cd ../ && \
    rm csmith-2.3.0.tar.gz

RUN wget https://github.com/intel/yarpgen/archive/refs/tags/v1.1.tar.gz && \
    tar -xzf v1.1.tar.gz && \
    cd yarpgen-1.1

# JAVA
RUN apt-get install -y --no-install-recommends openjdk-11-jre && \
    apt-get install ca-certificates-java -y && \
    apt-get clean && \
    update-ca-certificates -f;

RUN wget https://download.java.net/java/GA/jdk15.0.2/0d1cfde4252546c6931946de8db48ee2/7/GPL/openjdk-15.0.2_linux-x64_bin.tar.gz && \
    mkdir /usr/lib/java && \
    tar -xzf openjdk-15.0.2_linux-x64_bin.tar.gz -C /usr/lib/java

ENV PATH="/usr/lib/java/jdk-15.0.2/:${PATH}"

ENV JAVA_HOME="/usr/lib/java/jdk-15.0.2"

RUN update-alternatives --install "/usr/bin/java" "java" "/usr/lib/java/jdk-15.0.2/bin/java" 0 && \
    update-alternatives --install "/usr/bin/javac" "javac" "/usr/lib/java/jdk-15.0.2/bin/javac" 0 && \
    update-alternatives --install "/usr/bin/javap" "javap" "/usr/lib/java/jdk-15.0.2/bin/javap" 0 && \
    update-alternatives --set java /usr/lib/java/jdk-15.0.2/bin/java && \
    update-alternatives --set javac /usr/lib/java/jdk-15.0.2/bin/javac && \
    update-alternatives --set javap /usr/lib/java/jdk-15.0.2/bin/javap 

RUN wget https://github.com/rustsmith/rustsmith/releases/download/v1.30.0/rustsmith && \
    chmod 755 rustsmith && \
    mv rustsmith /usr/bin/

# RUN mkdir -p /data

# VOLUME ["/root/data"]



# CMD ["bash"]