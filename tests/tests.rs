use tsil_cev::TsilCev;

#[test]
fn test_push_back_front() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);
    tc.push_back(503);
    tc.push_back(504);
    tc.push_back(510);
    tc.push_back(508);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(504);
    tc.push_front(503);
    tc.push_front(502);
    tc.push_front(501);
    tc.push_front(500);

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![500, 501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510, 508];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());
}

#[test]
fn test_pop() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);
    tc.push_back(503);
    tc.push_back(504);
    tc.push_back(510);
    tc.push_back(508);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(504);
    tc.push_front(503);
    tc.push_front(502);
    tc.push_front(501);
    tc.push_front(500);

    tc.pop_front();
    tc.pop_back();

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let len = tc.len();
    tc.push_back(0);
    assert_eq!(tc.len(), len + 1);
    tc.push_back(1000);
    assert_eq!(tc.len(), len + 2);
    tc.push_back(1500);
    assert_eq!(tc.len(), len + 3);

    tc.pop_back();
    tc.pop_back();
    tc.pop_back();

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    tc.pop_front();
    tc.pop_front();
    tc.pop_front();
    tc.pop_front();

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![510, 508, 500, 501, 502, 503, 504, 510];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let tc = TsilCev::from_slice(&[
        501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510,
        501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510,
        501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510,
        501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510,
    ]);
    let mut tc_pop_back = tc.clone();
    while tc_pop_back.len() != 0 {
        tc_pop_back.pop_back();
    }

    let etalon = Vec::<usize>::new();
    assert_eq!(tc_pop_back.clone().to_vec(), etalon);
    assert_eq!(tc_pop_back.len(), etalon.len());
    assert_eq!(tc_pop_back.front(), etalon.first());
    assert_eq!(tc_pop_back.back(), etalon.last());

    let mut tc_pop_front = tc.clone();
    while tc_pop_front.len() != 0 {
        tc_pop_front.pop_front();
    }

    let etalon = Vec::<usize>::new();
    assert_eq!(tc_pop_front.clone().to_vec(), etalon);
    assert_eq!(tc_pop_front.len(), etalon.len());
    assert_eq!(tc_pop_front.front(), etalon.first());
    assert_eq!(tc_pop_front.back(), etalon.last());
}

#[test]
fn test_tsil_iter_stil() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(500);

    let mut v = vec![];
    for x in tc.iter_tsil() {
        v.push(x.clone());
    }
    let etalon = vec![500, 510, 508, 500, 501, 502];

    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());
}

#[test]
fn test_tsil_iter_cev() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(500);

    let mut v = vec![];
    for x in tc.iter_cev() {
        v.push(x.clone());
    }
    let mut etalon = vec![500, 510, 508, 500, 501, 502];
    v.sort();
    etalon.sort();

    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
}

#[test]
fn test_remove() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(500);

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![500, 510, 508, 500, 501, 502];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    tc.remove_if(|&x| x == 500);
    tc.remove_if(|&x| x == 501);

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![510, 508, 502];

    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let old_len = tc.len();
    tc.pop_back();
    tc.pop_back();
    assert_ne!(tc.len(), old_len);
    tc.push_back(5);
    tc.push_back(10);
    assert_eq!(tc.len(), etalon.len());
    tc.push_back(50);
    tc.push_back(100);
    tc.push_back(400);
    assert_eq!(tc.len(), old_len + 3);
}


#[test]
fn test_insert() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);
    tc.push_back(503);
    tc.push_back(504);
    tc.push_back(510);
    tc.push_back(508);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(504);
    tc.push_front(503);
    tc.push_front(502);
    tc.push_front(501);
    tc.push_front(500);

    tc.cursor_idx_mut(5).insert_after(1000);

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![500, 501, 502, 503, 504, 510, 1000, 508, 500, 501, 502, 503, 504, 510, 508];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let mut cursor = tc.cursor_front_mut()
        .insert_before(0)
        .move_next_length(2)
        .insert_before(1500)
        .finish();

    assert_eq!(Some(&mut 1500), cursor.peek_prev());
    assert_eq!(Some(&mut 502), cursor.inner_mut());
    assert_eq!(Some(&mut 503), cursor.peek_next());

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![0, 500, 501, 1500, 502, 503, 504, 510, 1000, 508, 500, 501, 502, 503, 504, 510, 508];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let mut cursor = tc.cursor_back_mut()
        .insert_before(0)
        .move_prev_length(2)
        .insert_before(1500)
        .finish();

    assert_eq!(Some(&mut 1500), cursor.peek_prev());
    assert_eq!(Some(&mut 510), cursor.inner_mut());
    assert_eq!(Some(&mut 0), cursor.peek_next());

    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![0, 500, 501, 1500, 502, 503, 504, 510, 1000, 508, 500, 501, 502, 503, 504, 1500, 510, 0, 508];
    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    tc.push_back(800);
    tc.push_front(200);
    let v = tc.iter_tsil().map(|x| x.clone()).collect::<Vec<_>>();
    let etalon = vec![200, 0, 500, 501, 1500, 502, 503, 504, 510, 1000, 508, 500, 501, 502, 503, 504, 1500, 510, 0, 508, 800];

    assert_eq!(v, etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());
    let old_len = tc.len();
    tc.pop_back();
    tc.pop_back();
    assert_ne!(tc.len(), old_len);
    tc.push_back(5);
    tc.push_back(10);
    assert_eq!(tc.len(), old_len);
}

#[test]
fn test_remove_balance() {
    let mut tc = TsilCev::with_capacity(64);
    for i in 0..64 {
        tc.push_back(i);
    }

    let mut cursor = tc.cursor_front_mut();
    let mut cnt = 0;
    while let Some(_) = cursor.inner() {
        cursor.remove();
        cnt += 1;
        if cnt == 50 {
            break;
        }
    }
    let etalon = (50..64).into_iter().map(|x| x).collect::<Vec<_>>();
    assert_eq!(tc.len(), 14);
    assert_eq!(tc.capacity(), 64 / 2);
    assert_eq!(tc.clone().to_vec(), etalon);

    let old_dencity = tc.len();
    tc.pop_back();
    tc.pop_back();
    assert_eq!(tc.len(), old_dencity - 2);
    tc.push_back(5);
    tc.push_back(10);
    assert_eq!(tc.len(), old_dencity);
}

#[test]
fn test_clear() {
    let mut tc = TsilCev::with_capacity(64);
    for i in 0..64 {
        tc.push_back(i);
    }

    tc.clear();

    tc.push_back(50);
    tc.push_front(500);
    tc.push_back(50);
    tc.push_front(500);
    tc.pop_back();
    tc.pop_front();

    let etalon = vec![500, 50];

    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    tc.pop_back();
    tc.clear();

    tc.push_back(50);
    tc.push_front(500);
    tc.push_back(50);
    tc.push_front(500);
    tc.pop_back();
    tc.pop_front();

    let etalon = vec![500, 50];

    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    tc.pop_back();
    tc.pop_back();
    tc.clear();

    tc.push_back(50);
    tc.push_front(500);
    tc.push_back(50);
    tc.push_front(500);
    tc.pop_back();
    tc.pop_front();

    let etalon = vec![500, 50];

    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());
}

#[test]
fn test_cursor_idx() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);
    tc.push_back(503);
    tc.push_back(504);
    tc.push_back(510);
    tc.push_back(508);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(504);
    tc.push_front(503);
    tc.push_front(502);
    tc.push_front(501);
    tc.push_front(500);

    let etalon = vec![500, 501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510, 508];

    assert_eq!(*tc.cursor_idx(3).inner().unwrap(), etalon[3]);
    assert_eq!(*tc.cursor_idx(11).inner().unwrap(), etalon[11]);
    assert_eq!(*tc.cursor_idx_mut(3).inner().unwrap(), etalon[3]);
    assert_eq!(*tc.cursor_idx_mut(11).inner().unwrap(), etalon[11]);

    let v = tc.to_vec();
    assert_eq!(v, etalon);
}

#[test]
fn test_to_vec() {
    let mut tc = TsilCev::new();
    tc.push_back(500);
    tc.push_back(501);
    tc.push_back(502);
    tc.push_back(503);
    tc.push_back(504);
    tc.push_back(510);
    tc.push_back(508);

    tc.push_front(508);
    tc.push_front(510);
    tc.push_front(504);
    tc.push_front(503);
    tc.push_front(502);
    tc.push_front(501);
    tc.push_front(500);

    let v = tc.to_vec();
    let etalon = vec![500, 501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510, 508];
    assert_eq!(v, etalon);
}

#[test]
fn test_from_slice() {
    let etalon = vec![500, 501, 502, 503, 504, 510, 508, 500, 501, 502, 503, 504, 510, 508];
    let mut tc = TsilCev::from_slice(&etalon);
    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    tc.push_back(100);
    tc.push_back(200);
    tc.push_back(300);
    tc.push_back(400);

    tc.push_front(1000);
    tc.push_front(2000);
    tc.push_front(3000);
    tc.push_front(4000);

    let etalon = vec![
        4000, 3000, 2000, 1000,
        500, 501, 502, 503, 504, 510, 508,
        500, 501, 502, 503, 504, 510, 508,
        100, 200, 300, 400
    ];
    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let etalon = vec![500, 501];
    let tc = TsilCev::from_slice(&etalon);
    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let etalon = vec![500];
    let tc = TsilCev::from_slice(&etalon);
    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());

    let etalon = Vec::<usize>::new();
    let tc = TsilCev::from_slice(&etalon);
    assert_eq!(tc.clone().to_vec(), etalon);
    assert_eq!(tc.len(), etalon.len());
    assert_eq!(tc.front(), etalon.first());
    assert_eq!(tc.back(), etalon.last());
}