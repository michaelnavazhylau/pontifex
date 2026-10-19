def update(error, integral, derivative, kp, ki, kd, dt):
    integral = integral + error * dt
    output = kp * error + ki * integral + kd * derivative
    return output, integral
