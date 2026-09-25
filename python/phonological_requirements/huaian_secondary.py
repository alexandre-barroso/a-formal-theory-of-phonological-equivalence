from pathlib import Path
import argparse
from . import huaian_observations, huaian_comparison, huaian_acoustics, huaian_original_counts, huaian_fit

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--book-data',required=True,type=Path)
    p.add_argument('--article-data',required=True,type=Path)
    p.add_argument('--work',required=True,type=Path)
    a=p.parse_args()
    a.work.mkdir(parents=True,exist_ok=True)
    for source in [a.book_data,a.article_data]:
        if a.work.resolve()==source.resolve() or source.resolve() in a.work.resolve().parents:
            raise ValueError('Choose an output directory outside the source-data directories')
    (a.work/'results').mkdir(exist_ok=True)
    huaian_observations.run(a.book_data,a.work)
    huaian_comparison.run(a.book_data,a.work)
    huaian_acoustics.run(a.book_data,a.work)
    huaian_original_counts.run(a.article_data,a.work)
    huaian_fit.run(a.book_data,a.work)

if __name__=='__main__':main()
