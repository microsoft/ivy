# Use an official Python runtime as a parent image
FROM python:2.7-slim

# Set the working directory to /app
WORKDIR /app

# Copy the current directory contents into the container at /app
COPY . /app
RUN mv /app/libz3.so /usr/local/lib


# Install any needed packages specified in requirements.txt
RUN apt-get update
RUN apt-get install libgomp1
RUN apt-get -y install net-tools iputils-ping iproute2 netcat
RUN pip install --trusted-host pypi.python.org -r requirements.txt

# Make port 80 available to the world outside this container
EXPOSE 4900-5199

# Define environment variable
ENV NAME World

# Run app.py when the container launches
# CMD ["python", "app.py"]
CMD ["/bin/bash"]