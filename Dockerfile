# Dockerfile for binder
# Reference: https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile

# Temporary work around: the first 8.2 image that was pushed to dockerhub was incompatible
FROM sagemath/sagemath:8.8

# Copy the contents of the repo in ${HOME}
COPY --chown=sage:sage . ${HOME}

## Getting ore_algebra pacakge
RUN git clone https://github.com/mkauers/ore_algebra/
RUN sage -pip install ./ore_algebra


# Install this package and dependencies
# RUN sage -pip install .
