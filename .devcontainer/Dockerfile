FROM ubuntu:22.04

ARG DEBIAN_FRONTEND=noninteractive
ARG USERNAME=vscode
ARG USER_UID=1000
ARG USER_GID=${USER_UID}

ENV TZ=Asia/Seoul

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    apt-transport-https \
    ca-certificates \
    curl \
    git \
    gnupg \
    software-properties-common \
    sudo \
    tar \
    tzdata \
    unzip \
    wget \
    z3 \
    zsh \
  && ln -snf /usr/share/zoneinfo/$TZ /etc/localtime \
  && echo $TZ >/etc/timezone \
  && dpkg-reconfigure -f noninteractive tzdata \
  && rm -rf /var/lib/apt/lists/*

RUN add-apt-repository ppa:deadsnakes/ppa -y \
  && apt-get update \
  && apt-get install -y --no-install-recommends \
    python3.12 \
    python3.12-dev \
    python3.12-venv \
  && curl -fsSL https://bootstrap.pypa.io/get-pip.py -o /tmp/get-pip.py \
  && python3.12 /tmp/get-pip.py \
  && python3.12 -m pip install --no-cache-dir "python-lsp-server[all]" \
  && rm -f /tmp/get-pip.py \
  && rm -rf /var/lib/apt/lists/*

RUN wget https://packages.microsoft.com/config/ubuntu/22.04/packages-microsoft-prod.deb -O /tmp/packages-microsoft-prod.deb \
  && dpkg -i /tmp/packages-microsoft-prod.deb \
  && rm -f /tmp/packages-microsoft-prod.deb \
  && apt-get update \
  && apt-get install -y --no-install-recommends dotnet-sdk-8.0 \
  && dotnet tool install --tool-path /usr/local/bin csharp-ls --version 0.16.0 \
  && rm -rf /var/lib/apt/lists/*

RUN groupadd --gid ${USER_GID} ${USERNAME} \
  && useradd --uid ${USER_UID} --gid ${USER_GID} -m ${USERNAME} \
  && usermod -aG sudo ${USERNAME} \
  && echo "${USERNAME} ALL=(ALL) NOPASSWD:ALL" >/etc/sudoers.d/${USERNAME} \
  && chmod 0440 /etc/sudoers.d/${USERNAME} \
  && chsh -s /usr/bin/zsh ${USERNAME}

RUN su - ${USERNAME} -c 'RUNZSH=no CHSH=no KEEP_ZSHRC=yes sh -c "$(curl -fsSL https://raw.githubusercontent.com/ohmyzsh/ohmyzsh/master/tools/install.sh)"'

RUN su - ${USERNAME} -c 'curl -fsSL https://opencode.ai/install | bash -s -- --no-modify-path'

ENV PATH="/home/${USERNAME}/.opencode/bin:${PATH}"

RUN sudo update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.12 1

USER ${USERNAME}
WORKDIR /workspaces/dafny

