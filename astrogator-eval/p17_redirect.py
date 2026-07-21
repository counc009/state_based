#!/usr/bin/python3
import os

models = ['deepseek', 'gpt', 'granite', 'llama', 'qwen', 'starcoder',
          'gpt-5-mini', 'gpt-oss', 'ministral', 'qwen3', 'qwen-coder']

for model in models:
  for i in range(0, 10):
    response = f'{model}/p17/response{i}.yml'
    original = f'{model}/p17/original{i}.yml'
    
    if os.path.isfile(original):
      print(f'{model} {i} - already processed')
    elif os.path.isfile(response):
      file = open(response, 'r')
      content = file.read()
      file.close()

      updated = content.replace('example.com', 'acc240.com')

      file = open(original, 'w')
      file.write(content)
      file.close()

      file = open(response, 'w')
      file.write(updated)
      file.close()
      print(f'{model} {i} - updated')
    else:
      print(f'{model} {i} - syntax error')
