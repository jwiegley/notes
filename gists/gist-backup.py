import os
import requests
import subprocess

def download_all_gists(username, dest_dir="gists", github_token=None):
    """
    Downloads all gists for the given GitHub username.
    
    Args:
        username (str): Your GitHub username.
        dest_dir (str): Directory to download gists into.
        github_token (str, optional): Personal access token for authentication.
    """
    os.makedirs(dest_dir, exist_ok=True)
    page = 1
    headers = {"Accept": "application/vnd.github+json"}
    if github_token:
        headers["Authorization"] = f"Bearer {github_token}"

    while True:
        url = f"https://api.github.com/users/{username}/gists?per_page=100&page={page}"
        response = requests.get(url, headers=headers)
        if response.status_code != 200:
            print(f"Failed to fetch gists: {response.status_code}")
            break
        gists = response.json()
        if not gists:
            break
        for gist in gists:
            gist_id = gist["id"]
            git_url = gist["git_pull_url"]
            gist_path = os.path.join(dest_dir, gist_id)
            if not os.path.exists(gist_path):
                print(f"Cloning gist {gist_id}...")
                subprocess.run(["git", "clone", git_url, gist_path])
            else:
                print(f"Gist {gist_id} already exists, skipping.")
        page += 1

download_all_gists("jwiegley", dest_dir=".", github_token=os.environ['GITHUB_TOKEN'])
